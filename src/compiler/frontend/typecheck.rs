use anyhow::{anyhow, bail, Context};

use super::{
    cst::{Actor, Cst, Expr, Forall, ForallElim, RecordType, Statement, TypeExpr, Update},
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

#[derive(Debug, Clone, Eq, PartialEq)]
enum Nominal {
    Opaque(usize, Vec<(String, Kind)>),
    Transparent(usize, TypeExpr),
}

#[derive(Debug)]
pub struct TypeChecker {
    globals: HashMap<String, TypeExpr>,
    blocks: Vec<Block>,
    aliases: HashMap<String, Nominal>,
    idx: usize,
    records: HashMap<usize, RecordType>,
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

        let mut idx = 0;
        let mut intrinsics = HashMap::new();

        for t in base_types {
            idx += 1;
            intrinsics.insert(t, Nominal::Opaque(idx, vec![]));
        }

        let mut s = Self {
            globals,
            blocks: Vec::new(),
            aliases: intrinsics,
            idx,
            records: HashMap::new(),
        };

        for (name, t) in aliases {
            match t {
                TypeExpr::RecordType(r) => {
                    s.declare_record(name, vec![], r);
                }
                TypeExpr::Forall(Forall { vars, then })
                    if matches!(*then, TypeExpr::RecordType(_)) =>
                {
                    let TypeExpr::RecordType(r) = *then else {
                        unreachable!();
                    };
                    s.declare_record(name, vars, r);
                }
                other => {
                    s.declare_structural(name, other);
                }
            }
        }

        // TODO: Validate aliases after all have been declared
        s
    }

    fn declare_record(&mut self, name: String, vars: Vec<(String, Kind)>, r: RecordType) -> usize {
        let rc = r.clone();
        let id = self.declare_opaque(name, vars);
        self.records.insert(id, rc);

        id
    }

    fn declare_opaque(&mut self, name: String, vars: Vec<(String, Kind)>) -> usize {
        self.aliases.insert(name, Nominal::Opaque(self.idx, vars));
        self.idx += 1;
        self.idx - 1
    }

    fn declare_structural(&mut self, name: String, t: TypeExpr) -> usize {
        self.aliases.insert(name, Nominal::Transparent(self.idx, t));
        self.idx += 1;
        self.idx - 1
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

        for actor in cst.actors {
            tc.validate_actor(actor)?;
        }
        Ok(tc)
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
            TypeExpr::TypeVar(n) => write!(f, "{n}"),
            TypeExpr::ForallElim(forall_elim) => write!(
                f,
                "{}[{}]",
                *forall_elim.expr,
                type_arg_list(&forall_elim.args)
            ),
            TypeExpr::RecordType(RecordType { fields }) => {
                write!(f, "{{")?;
                let fields = fields.iter().collect::<Vec<_>>();
                let Some((name, (_, t))) = fields.get(0) else {
                    return write!(f, "}}");
                };
                write!(f, "{name} : {t}")?;
                for (name, (_, t)) in &fields[1..] {
                    write!(f, ", {name} : {t}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

fn typevar_arg_list(args: &[(String, Kind)]) -> String {
    let [(first, first_kind), args @ ..] = args else {
        return String::new();
    };
    args.iter()
        .fold(format!("{first}:{first_kind}"), |acc, (name, kind)| {
            format!("{acc}, {name}:{kind}")
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

pub type Result<T> = anyhow::Result<T>;

fn base_type(name: &str) -> TypeExpr {
    TypeExpr::Base(name.to_string())
}

impl TypeChecker {
    fn get_alias(&self, name: &str) -> Result<&Nominal> {
        self.aliases
            .get(name)
            .with_context(|| format!("Unknown type: `{name}`"))
    }

    fn type_kind(&mut self, type_: &TypeExpr) -> Result<Kind> {
        match type_ {
            TypeExpr::Base(name) => {
                let c = self.get_alias(&name)?.clone();
                match c {
                    Nominal::Opaque(_, kind) => {
                        if kind.len() == 0 {
                            Ok(Kind::Type)
                        } else {
                            Ok(Kind::Function {
                                args: kind.iter().map(|(_, k)| k.clone()).collect(),
                                output: Box::new(Kind::Type),
                            })
                        }
                    }
                    Nominal::Transparent(_, e) => self.type_kind(&e),
                }
            }
            TypeExpr::RecordType(r) => {
                for (_, t) in r.fields.values() {
                    self.ensure_type(t.clone())?;
                }
                Ok(Kind::Type)
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
                self.ensure_type(*forall.then.clone())?;
                self.pop_block();
                Ok(Kind::Function {
                    args,
                    output: Box::new(Kind::Type),
                })
            }
            TypeExpr::ForallElim(forall_elim) => match self.type_kind(&forall_elim.expr)? {
                Kind::Type => Err(anyhow!(
                    "Expected `{}` to be a constructor to be applied to `{}`",
                    forall_elim.expr,
                    type_arg_list(&forall_elim.args)
                )),
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
            bail!(
                "Type arguments `{}` were given to a type abstraction `{}`",
                type_arg_list(&given),
                Kind::Function {
                    args: want.clone(),
                    output: Box::new(Kind::Type)
                }
            )
        }
        for (given, wanted) in given.into_iter().zip(want.into_iter()) {
            let given_kind = self.type_kind(&given)?;
            if given_kind != wanted {
                bail!("Expected type `{given}` to have kind {wanted}, but instead it has kind {given_kind}")
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
            TypeExpr::RecordType(RecordType { fields }) => {
                let new_fields: Result<HashMap<String, (usize, TypeExpr)>> = fields
                    .into_iter()
                    .map(|(name, (offset, t))| {
                        Ok((
                            name,
                            (
                                offset,
                                self.substitute_typevar(t, with.clone(), var_name.clone())?,
                            ),
                        ))
                    })
                    .collect();

                Ok(TypeExpr::RecordType(RecordType {
                    fields: new_fields?,
                }))
            }
        }
    }

    fn elim_forall(&mut self, fe: ForallElim<TypeExpr>) -> Result<TypeExpr> {
        let args: Result<Vec<TypeExpr>> =
            fe.args.iter().map(|a| self.simplify(a.clone())).collect();
        let args = args?;
        let kinds: Vec<(TypeExpr, Kind)> = fe
            .args
            .iter()
            .map(|arg| Ok((arg.clone(), self.type_kind(arg)?)))
            .collect::<Result<_>>()?;
        let wanted_kind = Kind::Function {
            args: kinds.iter().map(|(_, k)| k.clone()).collect(),
            output: Box::new(Kind::Type),
        };

        let f = match self.simplify(fe.expr.as_ref().clone())? {
            TypeExpr::Forall(f) => f,
            TypeExpr::Base(name) => {
                let Kind::Function { args, output: _ } =
                    self.type_kind(&TypeExpr::Base(name.clone()))?
                else {
                    bail!("Type `{name}` was expected to have kind `{wanted_kind}`, but instead has kind `*`");
                };

                for ((have, have_kind), want_kind) in kinds.into_iter().zip(args) {
                    if have_kind != want_kind {
                        bail!("Type `{have}` was expected to have kind `{want_kind}`, but instead has kind `{have_kind}`");
                    }
                }

                return Ok(TypeExpr::ForallElim(fe));
            }
            other => bail!("Expected type `{}` to have kind `{wanted_kind}` to be applied to type arguments, but instead it has kind `{}`", other, /*self.type_kind(&other)?*/ "cock"),
        };

        let zipped: Vec<_> = args.into_iter().zip(f.vars.into_iter()).collect();

        let mut subbed = *f.then;
        for (arg, (name, kind)) in zipped {
            if self.type_kind(&arg)? != kind {
                todo!();
            }
            subbed = self.substitute_typevar(subbed, arg, name)?;
        }
        let t = self.simplify(subbed)?;
        self.ensure_type(t.clone())?;
        Ok(t)
    }

    fn simplify(&mut self, type_: TypeExpr) -> Result<TypeExpr> {
        match type_ {
            TypeExpr::Base(name) => {
                if let Some(e) = self.aliases.get(&name) {
                    match e {
                        Nominal::Transparent(_, t) => self.simplify(t.clone()),
                        Nominal::Opaque(_, _) => Ok(TypeExpr::Base(name)),
                    }
                } else {
                    Err(anyhow!("Unknown type `{name}`"))
                }
            }
            TypeExpr::Forall(_) => Ok(type_),
            TypeExpr::Universal(_) => Ok(type_),
            TypeExpr::TypeVar(t) => Ok(TypeExpr::TypeVar(t)),
            TypeExpr::Actor(t) => Ok(TypeExpr::Actor(Box::new(self.simplify(*t)?))),
            TypeExpr::ForallElim(forall_elim) => {
                if let TypeExpr::Base(n) = *(forall_elim.expr.clone()) {
                    match self.get_alias(&n)?.clone() {
                        Nominal::Opaque(_, opaque_args) => {
                            let given: Result<Vec<_>> = forall_elim
                                .args
                                .iter()
                                .cloned()
                                .map(|a| self.type_kind(&a))
                                .collect();

                            let given = given?;

                            if given
                                != opaque_args
                                    .iter()
                                    .map(|(_, k)| k.clone())
                                    .collect::<Vec<_>>()
                            {
                                panic!("{given:?}, want {opaque_args:?}")
                            }
                            return Ok(TypeExpr::ForallElim(forall_elim));
                        }
                        _ => (),
                    };
                }
                self.elim_forall(forall_elim)
            }
            TypeExpr::RecordType(RecordType { fields }) => {
                let fields: Result<_> = fields
                    .into_iter()
                    .map(|(name, (offset, t))| Ok((name, (offset, self.simplify(t)?))))
                    .collect();
                Ok(TypeExpr::RecordType(RecordType { fields: fields? }))
            }
        }
    }

    fn types_match(&mut self, have_e: Expr, have: TypeExpr, want: TypeExpr) -> Result<()> {
        let have_s = self.simplify(have)?;
        let want_s = self.simplify(want)?;

        match (&have_s, &want_s) {
            (TypeExpr::Base(h), TypeExpr::Base(w)) => {
                let h = self
                    .aliases
                    .get(h)
                    .with_context(|| anyhow!("Unknown type `{h}`"))?;
                let w = self
                    .aliases
                    .get(w)
                    .with_context(|| anyhow!("Unknown type `{w}`"))?;
                match (h, w) {
                    (Nominal::Opaque(i, _), Nominal::Opaque(u, _)) => {
                        if i != u {
                            bail!("Expected `{have_e}` to have type `{want_s}`, but instead it has type `{have_s}`")
                        } else {
                            return Ok(());
                        }
                    }
                    _ => (),
                }
            }
            _ => (),
        }

        if have_s != want_s {
            Err(anyhow!(
                "Expected `{have_e}` to have type `{want_s}`, but instead it has type `{have_s}`"
            ))
        } else {
            Ok(())
        }
    }

    fn ensure_type(&mut self, type_: TypeExpr) -> Result<()> {
        match self.type_kind(&type_)? {
            Kind::Function { args: _, output: _ } => {
                Err(anyhow!("Expected type `{type_}` to have kind `*`"))
            }
            Kind::Type => Ok(()),
        }
    }

    fn validate_stmt(&mut self, stmt: Statement) -> Result<bool> {
        if self.current_block().finalised {
            return Ok(true);
        }
        match stmt {
            Statement::Assignment(a) => {
                let right_type = self.expr_type(a.right.clone())?;
                if let Some(t) = a.type_.clone() {
                    self.ensure_type(t.clone())?;
                    self.types_match(a.right, right_type.clone(), t)?;
                }
                self.declare_var(a.left, right_type)?;
                Ok(false)
            }
            Statement::Intrinsic { func_name: _, args } => {
                for e in args {
                    let _ = self.expr_type(e)?;
                }
                Ok(false)
            }
            Statement::Return(expr) => {
                let got_t = self.expr_type(expr.clone())?;
                let ret_t = self.current_block().return_type.clone();
                match self.types_match(expr, got_t, ret_t) {
                    Ok(()) => {
                        self.current_block_mut().finalised = true;
                        Ok(true)
                    }
                    Err(e) => Err(e),
                }
            }
            Statement::Actor(a) => {
                self.validate_actor(a)?;
                Ok(false)
            }
            Statement::Send { destination, value } => {
                let sent_t = self.expr_type(value.clone())?;
                let dest_t = self.expr_type(destination.clone())?;
                let dest_t_arg = match dest_t.clone() {
                    TypeExpr::Actor(a) => *a,
                    _ => {
                        bail!("Expected `{destination}` to have type `{}`, but instead it has type `{dest_t}`", TypeExpr::Actor(Box::new(sent_t.clone())));
                    }
                };
                self.types_match(value, sent_t, dest_t_arg)?;
                Ok(false)
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
                Ok(false)
            }
        }
    }

    fn validate_block(&mut self, stmts: impl Iterator<Item = Statement>) -> Result<bool> {
        self.push_block();
        for s in stmts {
            match self.validate_stmt(s) {
                Err(e) => {
                    self.pop_block();
                    return Err(e);
                }
                Ok(t) if t => break,
                Ok(_) => continue,
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
            TypeExpr::Universal(_) => Err(anyhow!("Expected type `{type_}` to have kind `*`")),
            TypeExpr::ForallElim(_) => {
                let t = self.simplify(type_)?;
                self.eq_func_name(t)
            }
            TypeExpr::TypeVar(_) => Err(anyhow!("Expected type `{type_}` to have kind `*`")),
            TypeExpr::Forall(_) => Err(anyhow!("Expected type `{type_}` to have kind `*`")),
            TypeExpr::RecordType(_record_type) => todo!(),
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
                    other => Err(anyhow!("Expected `{}` to have type `{wanted_t}`, but instead it has type `{other}`", *f.expr))
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
            Expr::Record(re) => {
                let r = self.extract_record(re.t.clone(), Expr::Record(re.clone()))?;
                *re.actual.borrow_mut() = Some(r.clone());
                let rec_type_fields: Result<Vec<_>> = re
                    .fields
                    .iter()
                    .map(|(name, e)| {
                        Ok((
                            name,
                            e,
                            &r.fields
                                .get(name)
                                .with_context(|| anyhow!("Type `{}` does not have field {name}", re.t.clone()))?
                                .1,
                        ))
                    })
                    .collect();

                let t: Result<()> = r
                    .fields
                    .keys()
                    .map(|f| {
                        if !re.fields.contains_key(f) {
                            Err(anyhow!("Type `{}` has field {f}, but it was missing during construction", re.t.clone()))
                        } else {
                            Ok(())
                        }
                    })
                    .collect();
                let _ = t?;

                let rtf = rec_type_fields?;

                for (_, e, t) in rtf {
                    let et = self.expr_type(e.clone())?;
                    self.types_match(e.clone(), et, t.clone())?;
                }

                Ok(re.t)
            }
            Expr::FieldAccess {
                from,
                offset,
                fieldname,
            } => {
                let from_t = self.expr_type(*(from.clone()))?;
                let rec_t = self.extract_record(from_t.clone(), *from)?;
                let (got_offset, t) =
                    rec_t
                        .fields
                        .get(&fieldname)
                        .with_context(|| anyhow!("Type `{from_t}` does not have field `{fieldname}`"))?;
                *offset.borrow_mut() = *got_offset;
                Ok(t.clone())
            }
        }
        .and_then(|t| self.simplify(t))
    }

    fn get_record(&self, name: &str) -> Result<RecordType> {
        match self.get_alias(name)? {
            Nominal::Opaque(id, _) => self
                .records
                .get(id)
                .cloned()
                .with_context(|| anyhow!("Record constructor `{name}` is unbound")),
            _ => Err(anyhow!("Record constructor `{name}` is unbound")),
        }
    }

    fn extract_record(&mut self, t: TypeExpr, e: Expr) -> Result<RecordType> {
        match self.simplify(t)? {
            TypeExpr::Base(b) => self.get_record(&b),
            TypeExpr::ForallElim(ForallElim { expr, args }) => {
                let TypeExpr::Base(n) = *expr else { panic!() };
                let r = self.get_record(&n)?;
                let Nominal::Opaque(_, vars) = self
                    .aliases
                    .get(&n)
                    .expect(&format!("Record type {n} is a transparent alias"))
                else {
                    panic!("Record type {n} is a transparent alias")
                };

                let TypeExpr::RecordType(r) = self.elim_forall(ForallElim {
                    expr: Box::new(TypeExpr::Forall(Forall {
                        vars: vars.clone(),
                        then: Box::new(TypeExpr::RecordType(r)),
                    })),
                    args,
                })?
                else {
                    panic!();
                };
                Ok(r)
            }
            TypeExpr::RecordType(t) => Ok(t),
            other => {
                bail!(
                    "`{e}` was expected to have type `{}`, but instead has type `{other}`",
                    TypeExpr::RecordType(RecordType {
                        fields: HashMap::new()
                    })
                )
            }
        }
    }

    fn bind_typevar(&mut self, var_name: String, kind: Kind) {
        self.current_block_mut().declare_type_var(var_name, kind);
    }

    fn get_type_var(&self, var_name: &str) -> Result<Kind> {
        self.current_block()
            .var_kind(var_name)
            .with_context(|| anyhow!("Type variable `{var_name}` is unbound"))
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
                    bail!("Expected `{right_e}` to have type `{left}`, but instead has type `{right}`")
                }
            }
        };

        if left != &left_t {
            bail!("Expected `{left_e}` to have type `{left_t}`, but instead has type `{left}`")
        }

        if right != &right_t {
            bail!("Expected `{right_e}` to have type `{right_t}`, but instead has type `{right}`")
        }

        Ok(out_t)
    }

    fn var_type(&self, var: &str) -> Result<&TypeExpr> {
        match self.globals.get(var) {
            Some(t) => Some(t),
            None => self.blocks.last().and_then(|b| b.var_type(var)),
        }
        .with_context(|| anyhow!("Unbound variable: `{var}`"))
    }

    fn validate_actor(&mut self, actor: Actor) -> Result<()> {
        let state_type = actor.state.type_;
        self.ensure_type(state_type.clone())?;

        self.push_block();
        self.current_block_mut().return_type = state_type.clone();
        let init_returns = self.validate_block(actor.initialiser.body.iter().cloned())?;
        if !init_returns && state_type != base_type("Unit") {
            bail!("Actor `{}`'s initialiser does not return for all paths, and its return type is not `Unit`", actor.name)
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
            bail!("Actor `{}`'s updater does not return for all paths, and its return type is not `Unit`", actor.name)
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
