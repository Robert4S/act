use super::{
    cst::{Actor, Cst, Expr, Forall, ForallElim, Statement, TypeExpr, Update},
    tokenise::InfixToken,
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Display,
    iter,
    rc::Rc,
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Kind {
    Type,
    Function { args: Vec<Kind>, output: Box<Kind> },
}

#[derive(Debug)]
pub struct TypeChecker {
    globals: HashMap<String, TypeExpr>,
    blocks: Vec<Block>,
    aliases: HashMap<String, TypeExpr>,
    base_types: HashSet<String>,
}

impl TypeChecker {
    pub fn new(
        actors: &[Actor],
        aliases: HashMap<String, TypeExpr>,
        base_types: HashSet<String>,
    ) -> Self {
        let mut globals = HashMap::with_capacity(actors.len());
        for actor in actors {
            globals.insert(actor.name.clone(), Self::actor_type(actor.update.clone()));
        }
        Self {
            globals,
            base_types,
            blocks: Vec::new(),
            aliases,
        }
    }

    fn actor_type(updater: Update) -> TypeExpr {
        if updater.t_vars.len() > 0 {
            TypeExpr::Universal(Forall {
                vars: updater
                    .t_vars
                    .iter()
                    .cloned()
                    .zip(iter::repeat(Kind::Type))
                    .collect(),
                then: Box::new(TypeExpr::Actor(Box::new(updater.inp_type))),
            })
        } else {
            TypeExpr::Actor(Box::new(updater.inp_type))
        }
    }

    pub fn validate_prog(cst: Cst) -> Result<Self> {
        let mut tc = Self::new(&cst.actors, cst.aliases.clone(), cst.declarations);
        let aliases: Vec<(String, TypeExpr)> = tc
            .aliases
            .iter()
            .map(|(a, b)| (a.clone(), b.clone()))
            .collect();

        for (idx, alias) in aliases {
            print!(
                r#"Simplified {idx} from
        {alias}
            to
        "#
            );
            let t = tc.simplify(alias)?;
            println!("{t}");
            tc.aliases.insert(idx, t);
        }

        for actor in cst.actors {
            tc.validate_actor(actor)?;
        }
        Ok(tc)
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
    BlockFinalised,
    InitReturnMissing(String),
    UpdateReturnMissing(String),
    ApplicationToConcreteType(ForallElim<TypeExpr>),
    WrongForallElimArity {
        given: Vec<TypeExpr>,
        to: Vec<Kind>,
    },
    ExpectedConcrete(TypeExpr),
    KindMismatch {
        want: Kind,
        given: TypeExpr,
        given_kind: Kind,
    },
    UnboundTypeVar(String),
    UnknownBaseType(String),
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::UnboundVar(s) => write!(f, "Unbound variable `{s}`"),
            Error::Mismatched { want, got, expr } => write!(f, "`{expr:?}` was expected to have type `{want}`, but instead has type `{got}`"),
            Error::BlockFinalised => panic!(),
            Error::InitReturnMissing(name) => write!(f, "Actor `{name}`'s initialiser includes an implicit return, but it's return type is not `Unit`"),
            Error::UpdateReturnMissing(name) => write!(f, "Actor `{name}`'s updater includes an implicit return, but it's return type is not `Unit`"),
            Error::ApplicationToConcreteType(ForallElim { expr, args }) => write!(f, "Expected `{expr}` to be a constructor to be applied to `{}`", type_arg_list(args)),
            Error::WrongForallElimArity { given, to } => write!(f, "Type arguments `{}` were given to a type abstraction `{}`", type_arg_list(given), Kind::Function { args: to.clone(), output: Box::new(Kind::Type) }),
            Error::ExpectedConcrete(type_expr) => write!(f, "Expected `{type_expr}` to be a concrete type"),
            Error::KindMismatch { want, given, given_kind } => write!(f, "Type expression `{given}` was expected to have kind `{want}`, but instead has kind `{given_kind}`"),
            Error::UnboundTypeVar(n) => write!(f, "Type variable {n} is unbound"),
            Error::UnknownBaseType(n) => write!(f, "Reference to unknown base type {n}")
        }
    }
}

impl Display for TypeExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeExpr::Base(n) => write!(f, "{n}"),
            TypeExpr::Actor(type_expr) => write!(f, "Pid[{type_expr}]"),
            TypeExpr::Forall(forall) => {
                write!(f, "[{}]. {}", typevar_arg_list(&forall.vars), forall.then)
            }
            TypeExpr::Universal(forall) => {
                write!(f, "for ")?;
                write!(f, "[{}]. {}", typevar_arg_list(&forall.vars), forall.then)
            }
            TypeExpr::TypeVar(n) => write!(f, "'{n}"),
            TypeExpr::ForallElim(forall_elim) => write!(
                f,
                "{}[{}]",
                *forall_elim.expr,
                type_arg_list(&forall_elim.args)
            ),
        }
    }
}

fn typevar_arg_list(args: &[(String, Kind)]) -> String {
    let [(first, first_kind), args @ ..] = args else {
        return String::new();
    };
    args.iter()
        .fold(format!("'{first}:{first_kind}"), |acc, (name, kind)| {
            format!("{acc}, '{name}:{kind}")
        })
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Type => write!(f, "*"),
            Kind::Function { args, output } => {
                let args = args.clone();
                let mut args = args.iter();
                let first = args.next().unwrap();
                write!(f, "[{first}")?;
                for arg in args {
                    write!(f, ", {arg}")?;
                }
                write!(f, "] -> {output}")
            }
        }
    }
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
    fn type_kind(&mut self, type_: &TypeExpr) -> Result<Kind> {
        match type_ {
            TypeExpr::Base(name) => {
                if let Some(c) = self.aliases.get(name) {
                    self.type_kind(&c.clone())
                } else {
                    Ok(Kind::Type)
                }
            }
            TypeExpr::Actor(_) => Ok(Kind::Type),
            TypeExpr::Universal(forall) => {
                self.ensure_type(*forall.then.clone())?;
                Ok(Kind::Type)
            }
            TypeExpr::Forall(forall) => {
                self.push_block();
                for (name, kind) in &forall.vars {
                    self.bind_typevar(name.clone(), kind.clone());
                }
                let args = forall.vars.iter().map(|(_, kind)| kind).cloned().collect();
                let output = Box::new(self.type_kind(&forall.then)?);
                self.pop_block();
                Ok(Kind::Function { args, output })
            }
            TypeExpr::ForallElim(forall_elim) => match self.type_kind(&forall_elim.expr)? {
                Kind::Type => Err(Error::ApplicationToConcreteType(forall_elim.clone())),
                Kind::Function { args, output } => {
                    self.verify_elim_args(forall_elim.args.clone(), args)?;
                    Ok(*output)
                }
            },
            TypeExpr::TypeVar(n) => self.get_type_var(n),
        }
    }

    fn verify_elim_args(&mut self, given: Vec<TypeExpr>, want: Vec<Kind>) -> Result<()> {
        if given.len() != want.len() {
            return Err(Error::WrongForallElimArity { given, to: want });
        }
        for (given, wanted) in given.into_iter().zip(want.into_iter()) {
            let given_kind = self.type_kind(&given)?;
            if given_kind != wanted {
                return Err(Error::KindMismatch {
                    want: wanted,
                    given: given.clone(),
                    given_kind,
                });
            }
        }
        Ok(())
    }

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

    fn substitute_typevar(
        &mut self,
        into: TypeExpr,
        with: TypeExpr,
        var_name: String,
    ) -> Result<TypeExpr> {
        match into {
            TypeExpr::Base(_) => Ok(into),
            TypeExpr::TypeVar(n) if n == var_name => Ok(with),
            TypeExpr::TypeVar(_) => Ok(into),
            TypeExpr::Forall(f) => {
                if f.vars
                    .iter()
                    .any(|(name, _)| name.as_str() == var_name.as_str())
                {
                    return Ok(TypeExpr::Forall(f));
                }
                Ok(TypeExpr::Forall(Forall {
                    then: Box::new(self.substitute_typevar(*f.then.clone(), with, var_name)?),
                    ..f.clone()
                }))
            }
            TypeExpr::Universal(f) => {
                if f.vars
                    .iter()
                    .any(|(name, _)| name.as_str() == var_name.as_str())
                {
                    return Ok(TypeExpr::Universal(f));
                }
                Ok(TypeExpr::Universal(Forall {
                    then: Box::new(self.substitute_typevar(*f.then.clone(), with, var_name)?),
                    ..f.clone()
                }))
            }
            TypeExpr::Actor(texpr) => {
                let subbed = self.substitute_typevar(*texpr, with, var_name)?;
                Ok(TypeExpr::Actor(Box::new(subbed)))
            }
            TypeExpr::ForallElim(f) => {
                let args: Result<Vec<TypeExpr>> = f
                    .args
                    .into_iter()
                    .map(|a| self.substitute_typevar(a, with.clone(), var_name.clone()))
                    .collect();
                let body = Box::new(self.substitute_typevar(*f.expr, with, var_name)?);
                Ok(TypeExpr::ForallElim(ForallElim {
                    expr: body,
                    args: args?,
                }))
            }
        }
    }

    fn elim_forall(&mut self, fe: ForallElim<TypeExpr>) -> Result<TypeExpr> {
        let args: Result<Vec<TypeExpr>> = fe.args.into_iter().map(|a| self.simplify(a)).collect();
        let args = args?;

        let f = match self.simplify(*fe.expr)? {
            TypeExpr::Forall(f) => f,
            _ => panic!(),
        };

        let zipped: Vec<_> = args.into_iter().zip(f.vars.into_iter()).collect();

        let mut subbed = *f.then;
        for (arg, (name, kind)) in zipped {
            if self.type_kind(&arg)? != kind {
                todo!();
            }
            subbed = self.substitute_typevar(subbed, arg, name)?;
        }
        self.simplify(subbed)
    }

    fn simplify(&mut self, type_: TypeExpr) -> Result<TypeExpr> {
        match type_ {
            TypeExpr::Base(name) => {
                if let Some(e) = self.aliases.get(&name) {
                    Ok(self.simplify(e.clone())?)
                } else if self.base_types.contains(&name) {
                    Ok(TypeExpr::Base(name))
                } else {
                    Err(Error::UnknownBaseType(name))
                }
            }
            TypeExpr::Forall(_) => Ok(type_),
            TypeExpr::Universal(_) => Ok(type_),
            TypeExpr::TypeVar(t) => Ok(TypeExpr::TypeVar(t)),
            TypeExpr::Actor(t) => Ok(TypeExpr::Actor(Box::new(self.simplify(*t)?))),
            TypeExpr::ForallElim(forall_elim) => self.elim_forall(forall_elim),
        }
    }

    fn types_match(&mut self, have_e: Expr, have: TypeExpr, want: TypeExpr) -> Result<()> {
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

    fn ensure_type(&mut self, type_: TypeExpr) -> Result<()> {
        match self.type_kind(&type_)? {
            Kind::Function { args: _, output: _ } => Err(Error::ExpectedConcrete(type_)),
            Kind::Type => Ok(()),
        }
    }

    fn validate_stmt(&mut self, stmt: Statement) -> Result<()> {
        if self.current_block().finalised {
            return Err(Error::BlockFinalised);
        }
        match stmt {
            Statement::Assignment(a) => {
                self.ensure_type(a.type_.clone())?;
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
                let et = self.expr_type(condition.clone())?;
                self.types_match(condition, et, base_type("Bool"))?;
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
                Err(e) => {
                    self.pop_block();
                    return Err(e);
                }
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

    pub fn eq_func_name(&mut self, type_: TypeExpr) -> Result<String> {
        let res = match type_ {
            TypeExpr::Base(n) => Ok(format!("eval_eq_{}", n.to_lowercase())),
            TypeExpr::Actor(_) => Ok(format!("eval_eq_pid")),
            TypeExpr::Universal(_) => Err(Error::ExpectedConcrete(type_)),
            TypeExpr::ForallElim(_) => {
                let t = self.simplify(type_)?;
                self.eq_func_name(t)
            }
            TypeExpr::TypeVar(_) => Err(Error::ExpectedConcrete(type_)),
            TypeExpr::Forall(_) => Err(Error::ExpectedConcrete(type_)),
        };

        match res {
            Err(e) => {
                panic!("{e}");
            }
            _ => res,
        }
    }

    pub fn expr_type(&mut self, expr: Expr) -> Result<TypeExpr> {
        match expr {
            Expr::Float(_) => Ok(base_type("Float")),
            Expr::Int(_) => Ok(base_type("Int")),
            Expr::Bool(_) => Ok(base_type("Bool")),
            Expr::String(_) => Ok(base_type("String")),
            Expr::Symbol(s) => self.var_type(&s).cloned(),
            Expr::Infix {
                left,
                op,
                right,
                eq_typename_buf,
            } => {
                let left_t = self.expr_type(*left.clone())?;
                let right_t = self.expr_type(*right.clone())?;
                self.infix_type(&left_t, &right_t, op, eq_typename_buf, *left, *right)
            }
            Expr::ForallElim(f) => {
                let wanted_t = TypeExpr::Universal(Forall {
                    vars: (0..(f.args.len()))
                        .map(|n| (format!("a{n}"), Kind::Type))
                        .collect(),
                    then: Box::new(base_type("...")),
                });
                match self.expr_type(*f.expr.clone())? {
                    TypeExpr::Universal(forall) => self.elim_forall(ForallElim {
                        expr: forall.then,
                        args: f.args,
                    }),
                    other => Err(Error::Mismatched {
                        want: wanted_t,
                        got: other,
                        expr: *f.expr,
                    }),
                }
            }
            Expr::Forall(Forall { vars, then }) => {
                let vars: Vec<(String, Kind)> = vars
                    .into_iter()
                    .map(|(name, _)| name)
                    .zip(iter::repeat(Kind::Type))
                    .collect();
                self.push_block();
                vars.iter()
                    .for_each(|(name, kind)| self.bind_typevar(name.clone(), kind.clone()));
                let then_type = self.expr_type(*then)?;
                self.pop_block();
                Ok(TypeExpr::Universal(Forall {
                    vars,
                    then: Box::new(then_type),
                }))
            }
        }
        .and_then(|t| self.simplify(t))
    }

    fn bind_typevar(&mut self, var_name: String, kind: Kind) {
        self.current_block_mut().declare_type_var(var_name, kind);
    }

    fn get_type_var(&self, var_name: &str) -> Result<Kind> {
        self.current_block()
            .var_kind(var_name)
            .ok_or(Error::UnboundTypeVar(var_name.to_owned()))
            .cloned()
    }

    fn infix_type(
        &mut self,
        left: &TypeExpr,
        right: &TypeExpr,
        op: InfixToken,
        typename: Rc<RefCell<String>>,
        left_e: Expr,
        right_e: Expr,
    ) -> Result<TypeExpr> {
        let (left_t, right_t, out_t) = match op {
            InfixToken::Plus
            | InfixToken::Minus
            | InfixToken::Mul
            | InfixToken::Div
            | InfixToken::Mod => (base_type("Int"), base_type("Int"), base_type("Int")),
            InfixToken::PlusFloat
            | InfixToken::MinusFloat
            | InfixToken::MulFloat
            | InfixToken::DivFloat => (base_type("Float"), base_type("Float"), base_type("Float")),

            InfixToken::And | InfixToken::Or => {
                (base_type("Bool"), base_type("Bool"), base_type("Bool"))
            }
            InfixToken::GE | InfixToken::LE | InfixToken::Greater | InfixToken::Lesser => {
                (base_type("Int"), base_type("Int"), base_type("Bool"))
            }
            InfixToken::GEFloat
            | InfixToken::LEFloat
            | InfixToken::GreaterFloat
            | InfixToken::LesserFloat => {
                (base_type("Float"), base_type("Float"), base_type("Bool"))
            }
            InfixToken::Equal => {
                if left == right {
                    typename.replace_with(|_| self.eq_func_name(left.clone()).unwrap());
                    (left.clone(), left.clone(), base_type("Bool"))
                } else {
                    return Err(Error::Mismatched {
                        want: left.clone(),
                        got: right.clone(),
                        expr: right_e,
                    });
                }
            }
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
        self.ensure_type(state_type.clone())?;

        self.push_block();
        self.current_block_mut().return_type = state_type.clone();
        let init_returns = self.validate_block(actor.initialiser.body.iter().cloned())?;
        if !init_returns && state_type != base_type("Unit") {
            return Err(Error::InitReturnMissing(actor.name));
        }
        self.pop_block();

        let arg_type = actor.update.inp_type;
        self.ensure_type(arg_type.clone())?;
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
    type_vars: HashMap<String, Kind>,
    return_type: TypeExpr,
    finalised: bool,
}

impl Default for Block {
    fn default() -> Self {
        Self {
            variables: HashMap::new(),
            return_type: base_type("!"),
            finalised: false,
            type_vars: HashMap::new(),
        }
    }
}

impl Block {
    fn declare_type_var(&mut self, name: String, kind: Kind) {
        if self.type_vars.insert(name, kind).is_some() {
            panic!()
        }
    }

    fn var_kind(&self, name: &str) -> Option<&Kind> {
        self.type_vars.get(name)
    }

    fn var_type(&self, var: &str) -> Option<&TypeExpr> {
        self.variables.get(var)
    }

    fn declare_var(&mut self, name: String, type_: TypeExpr) {
        self.variables.insert(name, type_);
    }
}
