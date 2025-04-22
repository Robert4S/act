use super::{
    cst::{Actor, Expr, Forall, Statement, TypeExpr, Update},
    tokenise::InfixToken,
};
use std::{collections::HashMap, fmt::Display};

pub struct TypeChecker {
    globals: HashMap<String, TypeExpr>,
    blocks: Vec<Block>,
    constructors: HashMap<String, Forall>,
}

impl TypeChecker {
    fn new(actors: &[Actor], constructors: Vec<(String, Forall)>) -> Self {
        let mut globals = HashMap::with_capacity(actors.len());
        for actor in actors {
            globals.insert(actor.name.clone(), Self::actor_type(actor.update.clone()));
        }
        let constructors = constructors.into_iter().collect();
        Self {
            globals,
            constructors,
            blocks: Vec::new(),
        }
    }

    fn actor_type(updater: Update) -> TypeExpr {
        if updater.t_vars.len() > 0 {
            TypeExpr::Forall(Forall {
                vars: updater.t_vars,
                then: Box::new(TypeExpr::Actor(Box::new(updater.inp_type))),
            })
        } else {
            TypeExpr::Actor(Box::new(updater.inp_type))
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
    Mismatched {
        want: TypeExpr,
        got: TypeExpr,
        expr: Expr,
    },
    UnboundConstructor(String),
    BlockFinalised,
    InitReturnMissing(String),
    UpdateReturnMissing(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnboundVar(s) => write!(f, "Unbound variable {s}"),
            Error::Mismatched { want, got, expr } => write!(f, "{expr:?} was expected to have type {want}, but instead has type {got}"),
            Error::UnboundConstructor(s) => write!(f, "Unbound type constructor {s}"),
            Error::BlockFinalised => panic!(),
            Error::InitReturnMissing(name) => write!(f, "Actor {name}'s initialiser includes an implicit return, but it's return type is not Unit"),
            Error::UpdateReturnMissing(name) => write!(f, "Actor {name}'s updater includes an implicit return, but it's return type is not Unit"),
        }
    }
}

impl Display for TypeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpr::Base(n) => write!(f, "{n}"),
            TypeExpr::Actor(type_expr) => write!(f, "Pid({type_expr})"),
            TypeExpr::Forall(forall) => write!(
                f,
                "forall ({}). {}",
                typevar_arg_list(&forall.vars),
                forall.then
            ),
            TypeExpr::TypeVar(n) => write!(f, "'{n}"),
            TypeExpr::Constructor { name, args } => write!(f, "{name}({})", type_arg_list(&args)),
        }
    }
}

fn typevar_arg_list(args: &[String]) -> String {
    let [first, args @ ..] = args else {
        return String::new();
    };
    args.iter()
        .fold(first.clone(), |acc, arg| format!("{acc}, {arg}"))
}

fn type_arg_list(args: &[TypeExpr]) -> String {
    let [first, args @ ..] = args else {
        return String::new();
    };
    args.iter()
        .fold(first.to_string(), |acc, arg| format!("{acc}, {arg}"))
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

    fn elim_forall(&self, args: Vec<TypeExpr>, forall: Forall) -> Result<TypeExpr> {
        let arg_pairs = forall.vars.into_iter().zip(args.into_iter());

        let mut subbed = *forall.then;
        for (name, arg) in arg_pairs {
            subbed = self.substitute_typevar(subbed, arg, name)?;
        }
        Ok(self.simplify(subbed)?)
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
                self.elim_forall(args, constr)
            }
            TypeExpr::Actor(t) => Ok(TypeExpr::Actor(Box::new(self.simplify(*t)?))),
        }
    }

    fn types_match(&self, have_e: Expr, have: TypeExpr, want: TypeExpr) -> Result<()> {
        let have_s = self.simplify(have)?;
        let want_s = self.simplify(want)?;

        if have_s != want_s {
            Err(Error::Mismatched {
                want: want_s,
                got: have_s,
                expr: have_e,
            })
        } else {
            Ok(())
        }
    }

    fn validate_stmt(&mut self, stmt: Statement) -> Result<()> {
        if self.current_block().finalised {
            return Err(Error::BlockFinalised);
        }
        match stmt {
            Statement::Assignment(a) => {
                let right_type = self.expr_type(a.right.clone())?;
                self.types_match(a.right, right_type, a.type_.clone())?;
                self.declare_var(a.left, a.type_)?;
                Ok(())
            }
            Statement::Intrinsic {
                func_name: _,
                args: _,
            } => Ok(()),
            Statement::Return(expr) => {
                let got_t = self.expr_type(expr.clone())?;
                let ret_t = self.current_block().return_type.clone();
                match self.types_match(expr, got_t, ret_t) {
                    Ok(()) => {
                        self.current_block_mut().finalised = true;
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            }
            Statement::Actor(a) => self.validate_actor(a),
            Statement::Daemon(_) => panic!("Daemons are not supported"),
            Statement::Send { destination, value } => {
                let sent_t = self.expr_type(value.clone())?;
                let dest_t = self.expr_type(destination.clone())?;
                let dest_t_arg = match dest_t.clone() {
                    TypeExpr::Actor(a) => *a,
                    _ => {
                        return Err(Error::Mismatched {
                            want: TypeExpr::Actor(Box::new(sent_t.clone())),
                            got: dest_t,
                            expr: destination,
                        })
                    }
                };
                self.types_match(value, sent_t, dest_t_arg)
            }
            Statement::If {
                condition,
                body,
                otherwise,
            } => {
                self.types_match(
                    condition.clone(),
                    self.expr_type(condition)?,
                    base_type("Bool"),
                )?;
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
            }
        }
    }

    fn validate_block(&mut self, stmts: impl Iterator<Item = Statement>) -> Result<bool> {
        self.push_block();
        for s in stmts {
            match self.validate_stmt(s) {
                Err(Error::BlockFinalised) => break,
                Err(e) => return Err(e),
                _ => continue,
            }
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
                let left_t = self.expr_type(*left.clone())?;
                let right_t = self.expr_type(*right.clone())?;
                self.infix_type(&left_t, &right_t, op, *left, *right)
            }
            Expr::ForallElim { expr, args } => {
                let wanted_t = TypeExpr::Forall(Forall {
                    vars: (0..(args.len())).map(|n| format!("'a{n}")).collect(),
                    then: Box::new(base_type("...")),
                });
                match self.expr_type(*expr.clone())? {
                    TypeExpr::Forall(forall) => self.elim_forall(args, forall),
                    other => Err(Error::Mismatched {
                        want: wanted_t,
                        got: other,
                        expr: *expr,
                    }),
                }
            }
        }
        .and_then(|t| self.simplify(t))
    }

    fn infix_type(
        &self,
        left: &TypeExpr,
        right: &TypeExpr,
        op: InfixToken,
        left_e: Expr,
        right_e: Expr,
    ) -> Result<TypeExpr> {
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
                        expr: right_e,
                    });
                }
            }

            InfixToken::Assign => panic!(),
        };

        if left != &left_t {
            return Err(Error::Mismatched {
                want: left_t,
                got: left.clone(),
                expr: left_e,
            });
        }

        if right != &right_t {
            return Err(Error::Mismatched {
                want: right_t,
                got: right.clone(),
                expr: right_e,
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
