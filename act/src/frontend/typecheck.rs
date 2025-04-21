use super::{
    cst::{Actor, Expr, Forall, Statement, TypeExpr},
    tokenise::InfixToken,
};
use std::collections::HashMap;

pub struct TypeChecker {
    globals: HashMap<String, TypeExpr>,
    blocks: Vec<Block>,
    constructors: HashMap<String, Forall>,
}

impl TypeChecker {
    fn new(actors: &[Actor], constructors: Vec<(String, Forall)>) -> Self {
        let mut globals = HashMap::with_capacity(actors.len());
        for actor in actors {
            globals.insert(
                actor.name.clone(),
                TypeExpr::Actor(Box::new(actor.update.inp_type.clone())),
            );
        }
        let constructors = constructors.into_iter().collect();
        Self {
            globals,
            constructors,
            blocks: Vec::new(),
        }
    }

    pub fn validate_prog(actors: Vec<Actor>, constructors: Vec<(String, Forall)>) -> Result<()> {
        let mut tc = Self::new(&actors, constructors);
        for actor in actors {
            tc.validate_actor(actor)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub enum Error {
    UnboundVar(String),
    Mismatched { want: TypeExpr, got: TypeExpr },
    UnboundConstructor(String),
    BlockFinalised,
    InitReturnMissing(String),
    UpdateReturnMissing(String),
}

pub type Result<T> = core::result::Result<T, Error>;

fn base_type(name: &str) -> TypeExpr {
    TypeExpr::Base(name.to_string())
}

impl TypeChecker {
    fn current_block(&self) -> &Block {
        self.blocks.last().as_ref().unwrap()
    }

    fn current_block_mut(&mut self) -> &mut Block {
        self.blocks.last_mut().unwrap()
    }

    fn declare_var(&mut self, name: String, type_: TypeExpr) -> Result<()> {
        let type_ = self.simplify(type_)?;
        self.current_block_mut().declare_var(name, type_);
        Ok(())
    }

    fn create_constructor(&mut self, name: String, body: Forall) {
        self.constructors.insert(name, body);
    }

    fn get_constructor(&self, name: &str) -> Result<Forall> {
        self.constructors
            .get(name)
            .ok_or(Error::UnboundConstructor(name.to_string()))
            .cloned()
    }

    fn substitute_typevar(
        &self,
        into: TypeExpr,
        with: TypeExpr,
        var_name: String,
    ) -> Result<TypeExpr> {
        match into {
            TypeExpr::Base(_) => Ok(into),
            TypeExpr::TypeVar(n) if n == var_name => Ok(with),
            TypeExpr::TypeVar(_) => Ok(into),
            TypeExpr::Forall(f) => self.substitute_typevar(*f.then, with, var_name),
            TypeExpr::Constructor { name: _, args: _ } => {
                let simplified = self.simplify(into)?;
                self.substitute_typevar(simplified, with, var_name)
            }
            TypeExpr::Actor(texpr) => {
                let subbed = self.substitute_typevar(*texpr, with, var_name)?;
                Ok(TypeExpr::Actor(Box::new(subbed)))
            }
        }
    }

    fn simplify(&self, type_: TypeExpr) -> Result<TypeExpr> {
        match type_ {
            TypeExpr::Base(_) => Ok(type_),
            TypeExpr::Forall(Forall { vars, then }) => Ok(TypeExpr::Forall(Forall {
                vars,
                then: Box::new(self.simplify(*then)?),
            })),
            TypeExpr::TypeVar(_) => Ok(type_),
            TypeExpr::Constructor { name, args } => {
                let constr = self.get_constructor(&name)?;
                let arg_pairs = constr.vars.into_iter().zip(args.into_iter());

                let mut subbed = *constr.then;
                for (name, arg) in arg_pairs {
                    subbed = self.substitute_typevar(subbed, arg, name)?;
                }
                self.simplify(subbed)
            }
            TypeExpr::Actor(t) => Ok(TypeExpr::Actor(Box::new(self.simplify(*t)?))),
        }
    }

    fn validate_stmt(&mut self, stmt: Statement) -> Result<()> {
        if self.current_block().finalised {
            return Err(Error::BlockFinalised);
        }
        match stmt {
            Statement::Assignment(a) => {
                let right_type = self.expr_type(a.right)?;
                if right_type != a.type_ {
                    return Err(Error::Mismatched {
                        want: a.type_,
                        got: right_type,
                    });
                }
                self.declare_var(a.left, a.type_)?;
                Ok(())
            }
            Statement::Intrinsic {
                func_name: _,
                args: _,
            } => Ok(()),
            Statement::Return(expr) => {
                let got_t = self.expr_type(expr)?;
                let ret_t = self.current_block().return_type.clone();
                if ret_t == got_t {
                    self.current_block_mut().finalised = true;
                    Ok(())
                } else {
                    Err(Error::Mismatched {
                        want: ret_t,
                        got: got_t,
                    })
                }
            }
            Statement::Actor(a) => self.validate_actor(a),
            Statement::Daemon(_) => panic!("Daemons are not supported"),
            Statement::Send { destination, value } => {
                let sent_t = self.expr_type(value)?;
                let dest_t = self.expr_type(destination)?;
                let dest_t_arg = match dest_t {
                    TypeExpr::Actor(a) => *a,
                    _ => {
                        return Err(Error::Mismatched {
                            want: TypeExpr::Actor(Box::new(sent_t.clone())),
                            got: dest_t,
                        })
                    }
                };
                if sent_t == dest_t_arg {
                    Ok(())
                } else {
                    Err(Error::Mismatched {
                        want: dest_t_arg,
                        got: sent_t,
                    })
                }
            }
            Statement::If {
                condition,
                body,
                otherwise,
            } => {
                if self.expr_type(condition)? == base_type("Bool") {
                    let then_term = self.validate_block(body.iter().cloned())?;
                    let else_term = if let Some(otherwise) = otherwise {
                        self.validate_block(otherwise.iter().cloned())?
                    } else {
                        false
                    };
                    if then_term && else_term {
                        self.current_block_mut().finalised = true;
                    }
                    Ok(())
                } else {
                    Ok(())
                }
            }
        }
    }

    fn validate_block(&mut self, stmts: impl Iterator<Item = Statement>) -> Result<bool> {
        self.push_block();
        for s in stmts {
            self.validate_stmt(s)?;
        }
        let terminates = self.current_block().finalised;
        self.pop_block();
        Ok(terminates)
    }

    fn push_block(&mut self) {
        if self.blocks.len() == 0 {
            self.blocks.push(Block::default());
        } else {
            self.blocks.push(self.current_block().clone());
        }
    }

    fn pop_block(&mut self) -> Block {
        self.blocks.pop().unwrap()
    }

    fn expr_type(&self, expr: Expr) -> Result<TypeExpr> {
        match expr {
            Expr::Number(_) => Ok(base_type("Num")),
            Expr::Bool(_) => Ok(base_type("Bool")),
            Expr::String(_) => Ok(base_type("String")),
            Expr::Symbol(s) => self.var_type(&s).cloned(),
            Expr::Infix { left, op, right } => {
                let left = self.expr_type(*left)?;
                let right = self.expr_type(*right)?;
                self.infix_type(&left, &right, op)
            }
        }
    }

    fn infix_type(&self, left: &TypeExpr, right: &TypeExpr, op: InfixToken) -> Result<TypeExpr> {
        let (left_t, right_t, out_t) = match op {
            InfixToken::Plus | InfixToken::Minus | InfixToken::Mul | InfixToken::Div => {
                (base_type("Num"), base_type("Num"), base_type("Num"))
            }
            InfixToken::And | InfixToken::Or => {
                (base_type("Bool"), base_type("Bool"), base_type("Bool"))
            }
            InfixToken::GE | InfixToken::LE | InfixToken::Greater | InfixToken::Lesser => {
                (base_type("Num"), base_type("Num"), base_type("Bool"))
            }
            InfixToken::Equal => {
                if left == right {
                    (left.clone(), left.clone(), base_type("Bool"))
                } else {
                    return Err(Error::Mismatched {
                        want: left.clone(),
                        got: right.clone(),
                    });
                }
            }

            InfixToken::Assign => panic!(),
        };

        if left != &left_t {
            return Err(Error::Mismatched {
                want: left_t,
                got: left.clone(),
            });
        }

        if right != &right_t {
            return Err(Error::Mismatched {
                want: right_t,
                got: right.clone(),
            });
        }

        Ok(out_t)
    }

    fn var_type(&self, var: &str) -> Result<&TypeExpr> {
        match self.globals.get(var) {
            Some(t) => Some(t),
            None => self.blocks.last().and_then(|b| b.var_type(var)),
        }
        .ok_or(Error::UnboundVar(var.to_string()))
    }

    fn validate_actor(&mut self, actor: Actor) -> Result<()> {
        let state_type = actor.state.type_;

        self.push_block();
        self.current_block_mut().return_type = state_type.clone();
        let init_returns = self.validate_block(actor.initialiser.body.iter().cloned())?;
        if !init_returns && state_type != base_type("Unit") {
            return Err(Error::InitReturnMissing(actor.name));
        }
        self.pop_block();

        let arg_type = actor.update.inp_type;
        self.push_block();
        self.current_block_mut().return_type = state_type.clone();
        self.declare_var(actor.update.inp_name.clone(), arg_type)?;
        self.declare_var(actor.state.name.clone(), state_type.clone())?;

        let update_returns = self.validate_block(actor.update.body.iter().cloned())?;
        if !update_returns && state_type != base_type("Unit") {
            return Err(Error::UpdateReturnMissing(actor.name));
        }
        self.pop_block();
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Block {
    variables: HashMap<String, TypeExpr>,
    return_type: TypeExpr,
    finalised: bool,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            variables: HashMap::new(),
            return_type: base_type("!"),
            finalised: false,
        }
    }
}

impl Block {
    fn var_type(&self, var: &str) -> Option<&TypeExpr> {
        self.variables.get(var)
    }

    fn declare_var(&mut self, name: String, type_: TypeExpr) {
        self.variables.insert(name, type_);
    }
}
