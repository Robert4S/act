use super::{
    cst_typed::{Expr, Forall, Statement, TypeExpr},
    tokenise::InfixToken,
};
use std::collections::HashMap;

pub struct TypeChecker {
    globals: HashMap<String, TypeExpr>,
    blocks: Vec<Block>,
    constructors: HashMap<String, Forall>,
}

#[derive(Debug, Clone)]
pub enum Error {
    UnboundVar(String),
    Mismatched,
    UnboundConstructor(String),
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
        match with {
            TypeExpr::Base(_) => Ok(into),
            TypeExpr::TypeVar(n) if n == var_name => Ok(with),
            TypeExpr::Forall(f) => self.substitute_typevar(*f.then, with, var_name),
            TypeExpr::Constructor { name, args } => {
                let constr = self.get_constructor(&name)?;
                self.substitute_typevar(*constr.then, with, var_name)
            }
        }
    }

    fn simplify(&self, type_: TypeExpr) -> Result<TypeExpr> {
        match type_ {
            TypeExpr::Base(_) => Ok(type_),
            TypeExpr::Forall(Forall { var, then }) => Ok(TypeExpr::Forall(Forall {
                var,
                then: Box::new(self.simplify(*then)?),
            })),
            TypeExpr::TypeVar(_) => Ok(type_),
            TypeExpr::Constructor { name, args } => {
                let constr = self.get_constructor(&name)?;
            }
        }
    }

    fn validate_stmt(&mut self, stmt: Statement) -> Result<()> {
        match stmt {
            Statement::Assignment(a) => {
                let right_type = self.expr_type(a.right)?;
                if right_type != a.type_ {
                    return Err(Error::Mismatched);
                }
                self.declare_var(a.left, a.type_);
                Ok(())
            }
            Statement::Intrinsic {
                func_name: _,
                args: _,
            } => Ok(()),
            Statement::Return(expr) => {
                if self.expr_type(expr)? == self.current_block().return_type {
                    Ok(())
                } else {
                    Err(Error::Mismatched)
                }
            }
            Statement::Actor(actor) => todo!(),
            Statement::Daemon(actor) => todo!(),
            Statement::Send { destination, value } => match self.expr_type(destination)? {
                TypeExpr::Constructor { name, args }
                    if name.as_str() == "Pid" && args.len() == 1 =>
                {
                    if args[0] == self.expr_type(value)? {
                        Ok(())
                    } else {
                        Err(Error::Mismatched)
                    }
                }
                _ => Err(Error::Mismatched),
            },
            Statement::If {
                condition,
                body,
                otherwise,
            } => todo!(),
        }
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
                    return Err(Error::Mismatched);
                }
            }

            InfixToken::Assign => panic!(),
        };

        if (left, right) == (&left_t, &right_t) {
            Ok(out_t)
        } else {
            Err(Error::Mismatched)
        }
    }

    fn var_type(&self, var: &str) -> Result<&TypeExpr> {
        match self.globals.get(var) {
            Some(t) => Some(t),
            None => self.blocks.last().and_then(|b| b.var_type(var)),
        }
        .ok_or(Error::UnboundVar(var.to_string()))
    }
}

struct Block {
    variables: HashMap<String, TypeExpr>,
    return_type: TypeExpr,
}

impl Block {
    fn var_type(&self, var: &str) -> Option<&TypeExpr> {
        self.variables.get(var)
    }

    fn declare_var(&mut self, name: String, type_: TypeExpr) {
        self.variables.insert(name, type_);
    }
}
