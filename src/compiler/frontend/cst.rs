use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    f64::NAN,
    fmt::{Debug, Display},
    rc::Rc,
};

use crate::tokenise::{InfixToken, Token, TokenKind};

use super::typecheck;

macro_rules! consume {
    ($tokens:ident, $p:pat, $err:expr) => {
        #[allow(unused)]
        let ($p, $tokens) = (match $tokens {
            [(o, _), rest @ ..] if matches!(o, $p) => (o, rest),
            [(o, _), rest @ ..] => return make_error!($err, o.clone(), rest.to_vec().into()),
            _ => return make_error!($err, TokenKind::EOF, Vec::new()),
        }) else {
            unreachable!();
        };
    };
    ($tokens:ident, $p:pat) => {
        match $tokens {
            [(o, _), rest @ ..] if matches!(o, $p) => Some((o, rest)),
            _ => None,
        }
    };
    ($orig:ident, $rebind:ident, $p:pat, $err:expr) => {
        let $rebind = $orig;
        consume!($rebind, $p, $err);
    };
}

macro_rules! make_error {
    ($e:expr, $g:expr, $r:expr) => {
        Err(ParseError::WrongToken {
            expected: $e,
            got: $g,
            remaining: $r,
        })
    };
}

macro_rules! end_of_match {
    ($other:expr, $expected:expr) => {
        match $other {
            [(o, _), rest @ ..] => make_error!($expected, o.clone(), rest.to_vec().into()),
            _ => make_error!($expected, TokenKind::EOF, Vec::new()),
        }
    };
}

#[derive(Clone)]
pub enum ParseError {
    WrongToken {
        expected: TokenKind,
        got: TokenKind,
        remaining: Vec<Token>,
    },
    NoRuleMatch {
        expected: String,
        remaining: Vec<Token>,
    },
}

impl Debug for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongToken {
                expected,
                got,
                remaining,
            } => {
                let line_num = remaining.get(0).map(|(_, l)| l).unwrap_or(&0);
                write!(
                    f,
                    "Line {line_num}: Expected TOKEN({expected:?}), got TOKEN({got:?})"
                )
            }
            Self::NoRuleMatch {
                expected,
                remaining,
            } => {
                let line_num = remaining.get(0).map(|(_, l)| l).unwrap_or(&0);
                write!(
                    f,
                    "Line {line_num}: Expected RULE({expected}), but could not match any patterns"
                )
            }
        }
    }
}

type Result<T> = std::result::Result<T, ParseError>;

#[derive(Clone, Debug)]
pub struct Cst {
    pub actors: Vec<Actor>,
    pub aliases: HashMap<String, TypeExpr>,
    pub declarations: HashSet<String>,
}

#[derive(Debug, Clone)]
pub struct Actor {
    pub name: String,
    pub state: State,
    pub initialiser: Initialiser,
    pub update: Update,
}

#[derive(Debug, Clone)]
pub struct Update {
    pub t_vars: Vec<String>,
    pub inp_name: String,
    pub inp_type: TypeExpr,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct State {
    pub name: String,
    pub type_: TypeExpr,
}

#[derive(Debug, Clone)]
pub struct Initialiser {
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assignment(Assignment),
    Intrinsic {
        func_name: String,
        args: Vec<Expr>,
    },
    Return(Expr),
    Actor(Actor),
    Send {
        destination: Expr,
        value: Expr,
    },
    If {
        condition: Expr,
        body: Vec<Statement>,
        otherwise: Option<Vec<Statement>>,
    },
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub left: String,
    pub type_: Option<TypeExpr>,
    pub right: Expr,
}

pub trait ForallT {
    type Kind: Debug + Clone + Eq + PartialEq;

    fn parse_typevar(tokens: &[Token]) -> Result<((String, Self::Kind), &[Token])>;
}

impl ForallT for TypeExpr {
    type Kind = typecheck::Kind;
    fn parse_typevar(tokens: &[Token]) -> Result<((String, Self::Kind), &[Token])> {
        consume!(
            tokens,
            TokenKind::Symbol(name),
            TokenKind::Symbol("_".to_string())
        );
        match tokens {
            [(TokenKind::Lsquare, _), rest @ ..] => {
                let (args, rest) = parse_hkt_typevar_tail(rest)?;
                let kind = typecheck::Kind::Function {
                    args,
                    output: Box::new(typecheck::Kind::Type),
                };
                Ok(((name.clone(), kind), rest))
            }
            other => Ok(((name.clone(), typecheck::Kind::Type), other)),
        }
    }
}

fn parse_underscore(tokens: &[Token]) -> Result<&[Token]> {
    match tokens {
        [(TokenKind::Symbol(s), _), rest @ ..] if s.as_str() == "_" => Ok(rest),
        other => end_of_match!(other, TokenKind::Symbol(String::from("_"))),
    }
}

fn parse_hk_typevar(tokens: &[Token]) -> Result<(typecheck::Kind, &[Token])> {
    let tokens = parse_underscore(tokens)?;
    if let Some((_, rest)) = consume!(tokens, TokenKind::Lsquare) {
        let (args, rest) = parse_hkt_typevar_tail(rest)?;
        return Ok((
            typecheck::Kind::Function {
                args,
                output: Box::new(typecheck::Kind::Type),
            },
            rest,
        ));
    }

    Ok((typecheck::Kind::Type, tokens))
}

fn parse_hkt_typevar_tail(tokens: &[Token]) -> Result<(Vec<typecheck::Kind>, &[Token])> {
    let (e, tokens) = parse_hk_typevar(tokens)?;
    let mut args = vec![e];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rsquare, _), ..]) {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        let (e, rest) = parse_hk_typevar(rest)?;
        args.push(e);
        tokens = rest;
    }

    consume!(tokens, TokenKind::Rsquare, TokenKind::Rsquare);

    Ok((args, tokens))
}

impl ForallT for Expr {
    type Kind = typecheck::Kind;
    fn parse_typevar(tokens: &[Token]) -> Result<((String, Self::Kind), &[Token])> {
        consume!(
            tokens,
            TokenKind::Symbol(name),
            TokenKind::Symbol("_".to_string())
        );
        match tokens {
            [(TokenKind::Lsquare, _), rest @ ..] => {
                let (args, rest) = parse_hkt_typevar_tail(rest)?;
                let kind = typecheck::Kind::Function {
                    args,
                    output: Box::new(typecheck::Kind::Type),
                };
                Ok(((name.clone(), kind), rest))
            }
            other => Ok(((name.clone(), typecheck::Kind::Type), other)),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Forall<T: ForallT> {
    pub vars: Vec<(String, T::Kind)>,
    pub then: Box<T>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ForallElim<T> {
    pub expr: Box<T>,
    pub args: Vec<TypeExpr>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TypeExpr {
    Base(String),
    Actor(Box<TypeExpr>),
    Universal(Forall<TypeExpr>),
    Forall(Forall<TypeExpr>),
    ForallElim(ForallElim<TypeExpr>),
    TypeVar(String),
    RecordType(RecordType),
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct RecordType {
    pub fields: HashMap<String, (usize, TypeExpr)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordExpr {
    pub t: TypeExpr,
    pub fields: HashMap<String, Expr>,
    pub actual: Rc<RefCell<Option<RecordType>>>,
}

impl Display for RecordExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {{", self.t)?;
        let fields: Vec<_> = self.fields.iter().collect();
        write!(f, "{} = {}", &fields[0].0, &fields[0].1)?;
        for (name, value) in &fields[1..] {
            write!(f, ", {} = {}", name, value)?;
        }
        write!(f, "}}")
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Float(f64),
    Int(i64),
    String(String),
    Symbol(String),
    Bool(bool),
    Infix {
        left: Box<Expr>,
        op: InfixToken,
        right: Box<Expr>,
        eq_typename_buf: Rc<RefCell<String>>,
    },
    Forall(Forall<Expr>),
    ForallElim(ForallElim<Expr>),
    Record(RecordExpr),
    FieldAccess {
        from: Box<Expr>,
        offset: Rc<RefCell<usize>>,
        fieldname: String,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Float(fl) => write!(f, "{fl}"),
            Expr::Int(i) => write!(f, "{i}"),
            Expr::String(s) => write!(f, "\"{s}\""),
            Expr::Symbol(s) => write!(f, "{s}"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Infix {
                left,
                op,
                right,
                eq_typename_buf: _,
            } => write!(f, "{left} {op} {right}"),
            Expr::Forall(Forall { vars, then }) => {
                write!(f, "[{}:{}", &vars[0].0, &vars[0].1)?;
                for (name, kind) in &vars[1..] {
                    write!(f, ", {name}:{kind}")?;
                }
                write!(f, "]. {}", *then)
            }
            Expr::ForallElim(ForallElim { expr, args }) => {
                write!(f, "{expr}[{}", &args[0])?;
                for arg in &args[1..] {
                    write!(f, ", {arg}")?
                }
                write!(f, "]")
            }
            Expr::Record(record_expr) => write!(f, "{record_expr}"),
            Expr::FieldAccess {
                from,
                offset: _,
                fieldname,
            } => write!(f, "{from}.{fieldname}"),
        }
    }
}

fn parse_forall<T: ForallT>(
    tokens: &[Token],
    parse_t: impl Fn(&[Token]) -> Result<(T, &[Token])>,
) -> Result<(Forall<T>, &[Token])> {
    consume!(tokens, rest, TokenKind::Lsquare, TokenKind::Lsquare);

    let (vars, rest) = parse_forall_tail::<T>(rest)?;
    let (body, rest) = parse_t(rest)?;
    Ok((
        Forall::<T> {
            vars,
            then: Box::new(body),
        },
        rest,
    ))
}

fn parse_forall_tail<T: ForallT>(tokens: &[Token]) -> Result<(Vec<(String, T::Kind)>, &[Token])> {
    let (first, tokens) = T::parse_typevar(tokens)?;

    let mut vars = vec![first];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rsquare, _), ..]) {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        let (e, rest) = T::parse_typevar(rest)?;

        tokens = rest;
        vars.push(e);
    }

    consume!(tokens, TokenKind::Rsquare, TokenKind::Rsquare);
    consume!(tokens, TokenKind::Dot, TokenKind::Dot);

    Ok((vars, tokens))
}

fn parse_forall_elim(tokens: &[Token]) -> Result<(Vec<TypeExpr>, &[Token])> {
    let (e, tokens) = parse_type_expr(tokens)?;
    let mut exprs = vec![e];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rsquare, _), ..]) {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        let (e, rest) = parse_type_expr(rest)?;
        tokens = rest;
        exprs.push(e);
    }

    consume!(tokens, TokenKind::Rsquare, TokenKind::Rsquare);

    Ok((exprs, tokens))
}

pub fn parse(tokens: &[Token], cst: &mut Cst) -> Result<()> {
    let mut tokens = tokens;

    while !matches!(tokens, [(TokenKind::EOF, _)]) {
        match tokens {
            [(TokenKind::Type, _), (TokenKind::TypeName(name), _), (TokenKind::Assign, _), rest @ ..] =>
            {
                let (t, rest) = parse_type_expr(rest)?;
                cst.aliases.insert(name.clone(), t);
                consume!(rest, TokenKind::Semi, TokenKind::Semi);
                tokens = rest;
            }
            [(TokenKind::NewType, _), (TokenKind::TypeName(name), _), rest @ ..] => {
                cst.declarations.insert(name.clone());
                consume!(rest, TokenKind::Semi, TokenKind::Semi);
                tokens = rest
            }
            other => {
                let (actor, rest) = parse_actor(other)?;
                let actor = match actor {
                    Statement::Actor(a) => a,
                    o => panic!("nonono {o:?} is not an actor"),
                };
                cst.actors.push(actor);
                tokens = rest;
            }
        }
    }
    Ok(())
}

fn parse_record_type(tokens: &[Token]) -> Result<(TypeExpr, &[Token])> {
    consume!(tokens, TokenKind::Lbrac, TokenKind::Lbrac);
    let (fields, tokens) = parse_record_type_tail(tokens)?;
    let mut idx = 0;
    let mut field_map = HashMap::new();
    for (name, t) in fields {
        field_map.insert(name, (idx, t));
        idx += 1;
    }
    let e = TypeExpr::RecordType(RecordType { fields: field_map });
    Ok((e, tokens))
}

fn parse_record_type_tail(tokens: &[Token]) -> Result<(Vec<(String, TypeExpr)>, &[Token])> {
    consume!(
        tokens,
        TokenKind::Symbol(first_name),
        TokenKind::Symbol("field_name".into())
    );
    consume!(tokens, TokenKind::Colon, TokenKind::Colon);
    let (first_val, mut tokens) = parse_type_expr(tokens)?;

    let mut fields = vec![(first_name.clone(), first_val)];
    while consume!(tokens, TokenKind::Rbrac).is_none() {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        consume!(
            rest,
            TokenKind::Symbol(name),
            TokenKind::Symbol("field_name".into())
        );
        consume!(rest, TokenKind::Colon, TokenKind::Colon);
        let (e, rest) = parse_type_expr(rest)?;
        fields.push((name.clone(), e));
        tokens = rest;
    }

    consume!(tokens, TokenKind::Rbrac, TokenKind::Rbrac);
    Ok((fields, tokens))
}

fn parse_type_expr(tokens: &[Token]) -> Result<(TypeExpr, &[Token])> {
    fn parse_forall_type(tokens: &[Token]) -> Option<(TypeExpr, &[Token])> {
        let (f, rest) = parse_forall(tokens, parse_type_expr).ok()?;
        Some((TypeExpr::Forall(f), rest))
    }

    fn parse_record_type_inner(tokens: &[Token]) -> Option<(TypeExpr, &[Token])> {
        parse_record_type(tokens).ok()
    }

    let (parsed, rest) = match tokens {
        [(TokenKind::Lparen, _), rest @ ..] => {
            let (inner, rest) = parse_type_expr(rest)?;
            consume!(rest, TokenKind::Rparen, TokenKind::Rparen);
            Ok((inner, rest))
        }
        tokens => [
            parse_base_type,
            parse_forall_type,
            parse_typevar,
            parse_universal,
            parse_record_type_inner,
        ]
        .iter()
        .filter_map(|f| f(tokens))
        .next()
        .ok_or(ParseError::NoRuleMatch {
            expected: "Type expression".to_string(),
            remaining: tokens.iter().cloned().collect(),
        }),
    }?;

    parse_type_expr_tail(parsed, rest)
}

fn parse_type_expr_tail(parsed: TypeExpr, rest: &[Token]) -> Result<(TypeExpr, &[Token])> {
    match (rest, parsed) {
        ([(TokenKind::Lsquare, _), rest @ ..], TypeExpr::Base(s)) if s.as_str() == "Pid" => {
            let (arg, rest) = parse_type_expr(rest)?;
            consume!(rest, TokenKind::Rsquare, TokenKind::Rsquare);
            parse_type_expr_tail(TypeExpr::Actor(Box::new(arg)), rest)
        }
        ([(TokenKind::Lsquare, _), rest @ ..], parsed) => {
            let (args, tokens) = parse_forall_elim(rest)?;
            let elim = TypeExpr::ForallElim(ForallElim::<TypeExpr> {
                expr: Box::new(parsed),
                args,
            });

            parse_type_expr_tail(elim, tokens)
        }
        (rest, parsed) => Ok((parsed, rest)),
    }
}

fn parse_universal(tokens: &[Token]) -> Option<(TypeExpr, &[Token])> {
    let (_, rest) = consume!(tokens, TokenKind::Forall)?;

    let (body, rest) = parse_forall(rest, parse_type_expr).ok()?;

    Some((TypeExpr::Universal(body), rest))
}

fn parse_base_type(tokens: &[Token]) -> Option<(TypeExpr, &[Token])> {
    match tokens {
        [(TokenKind::TypeName(s), _), rest @ ..] => Some((TypeExpr::Base(s.clone()), rest)),
        _ => None,
    }
}

fn parse_typevar(tokens: &[Token]) -> Option<(TypeExpr, &[Token])> {
    if let [(TokenKind::Symbol(name), _), rest @ ..] = tokens {
        Some((TypeExpr::TypeVar(name.clone()), rest))
    } else {
        None
    }
}

fn parse_symbol(tokens: &[Token]) -> Result<(String, &[Token])> {
    consume!(
        tokens,
        TokenKind::Symbol(s),
        TokenKind::Symbol("".to_string())
    );

    Ok((s.clone(), tokens))
}

fn parse_actor(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    consume!(tokens, TokenKind::Actor, TokenKind::Actor);

    let (name, tokens) = parse_symbol(tokens)?;
    consume!(tokens, TokenKind::Lbrac, TokenKind::Lbrac);
    let (state, tokens) = parse_state(tokens)?;
    let (initialiser, tokens) = parse_initialiser(tokens)?;
    let (update, tokens) = parse_updater(tokens)?;
    consume!(tokens, TokenKind::Rbrac, TokenKind::Rbrac);
    Ok((
        Statement::Actor(Actor {
            name,
            state,
            update,
            initialiser,
        }),
        tokens,
    ))
}

fn parse_state(tokens: &[Token]) -> Result<(State, &[Token])> {
    consume!(tokens, TokenKind::State, TokenKind::State);
    consume!(
        tokens,
        TokenKind::Symbol(name),
        TokenKind::Symbol("".to_string())
    );
    consume!(tokens, TokenKind::Colon, TokenKind::Colon);
    let (type_, tokens) = parse_type_expr(tokens)?;
    consume!(tokens, TokenKind::Semi, TokenKind::Semi);
    Ok((
        State {
            type_,
            name: name.clone(),
        },
        tokens,
    ))
}

fn parse_initialiser(tokens: &[Token]) -> Result<(Initialiser, &[Token])> {
    consume!(tokens, TokenKind::Initialiser, TokenKind::Initialiser);
    let (statements, tokens) = parse_statement_block(tokens)?;
    let initialiser = Initialiser { body: statements };
    Ok((initialiser, tokens))
}

fn parse_statement_block(tokens: &[Token]) -> Result<(Vec<Statement>, &[Token])> {
    consume!(tokens, TokenKind::Lbrac, TokenKind::Lbrac);
    let mut statements = Vec::new();
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rbrac, _), ..]) {
        let (statement, rest) = parse_statement(tokens)?;
        consume!(rest, TokenKind::Semi, TokenKind::Semi);
        statements.push(statement);
        tokens = rest;
    }
    consume!(tokens, TokenKind::Rbrac, TokenKind::Rbrac);

    let statements = statements.into_iter().collect();
    Ok((statements, tokens))
}

fn parse_statement(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let fns = [
        parse_assignment,
        parse_actor,
        parse_return,
        parse_send,
        parse_if,
        parse_intrinsic,
    ];

    let res = fns.iter().filter_map(|f| f(tokens).ok()).next();

    if let Some(r) = res {
        Ok(r)
    } else {
        let errors = fns.iter().filter_map(|f| match f(tokens) {
            Err(e) => Some(e),
            _ => None,
        });
        let [(_, mut highest_line), ..] = tokens else {
            panic!()
        };
        let mut highest_error = None;
        for error in errors {
            match &error {
                ParseError::WrongToken {
                    expected: _,
                    got: _,
                    remaining,
                } if current_line(remaining) > highest_line => {
                    highest_error = Some(error.clone());
                    highest_line = current_line(remaining);
                }
                ParseError::NoRuleMatch {
                    expected: _,
                    remaining,
                } if current_line(remaining) > highest_line => {
                    highest_error = Some(error.clone());
                    highest_line = current_line(remaining);
                }
                _ => (),
            }
        }
        if let Some(e) = highest_error {
            Err(e)
        } else {
            Err(ParseError::NoRuleMatch {
                expected: "Statement".to_string(),
                remaining: tokens.iter().cloned().collect(),
            })
        }
    }
}

fn current_line(tokens: &Vec<Token>) -> usize {
    tokens[0].1
}

fn parse_if(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    consume!(tokens, TokenKind::If, TokenKind::If);
    let (condition, tokens) = parse_expr(tokens)?;
    let (body, tokens) = parse_statement_block(tokens)?;
    let (otherwise, tokens) = parse_else(tokens)?;
    Ok((
        Statement::If {
            condition,
            body,
            otherwise,
        },
        tokens,
    ))
}

fn parse_else(tokens: &[Token]) -> Result<(Option<Vec<Statement>>, &[Token])> {
    match tokens {
        [(TokenKind::Else, _), rest @ ..] => {
            let (statements, tokens) = parse_statement_block(rest)?;
            Ok((Some(statements), tokens))
        }
        _ => Ok((None, tokens)),
    }
}

fn parse_intrinsic(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    consume!(tokens, TokenKind::Intrinsic, TokenKind::Intrinsic);
    consume!(tokens, TokenKind::Lparen, TokenKind::Lparen);
    let (func_name, tokens) = parse_symbol(tokens)?;
    consume!(tokens, TokenKind::Comma, TokenKind::Comma);
    let (args, tokens) = parse_intrinsic_tail(tokens)?;

    Ok((Statement::Intrinsic { func_name, args }, tokens))
}

fn parse_intrinsic_tail(tokens: &[Token]) -> Result<(Vec<Expr>, &[Token])> {
    let (e, tokens) = parse_expr(tokens)?;
    let mut exprs = vec![e];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rparen, _), ..]) {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        let (e, rest) = parse_expr(rest)?;
        tokens = rest;
        exprs.push(e);
    }
    consume!(tokens, TokenKind::Rparen, TokenKind::Rparen);

    Ok((exprs, tokens))
}

fn parse_assignment(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    consume!(tokens, TokenKind::Let, TokenKind::Let);
    let (name, tokens) = parse_symbol(tokens)?;
    let (type_, tokens) = if let Some((_, tokens)) = consume!(tokens, TokenKind::Colon) {
        let (type_, tokens) = parse_type_expr(tokens)?;
        (Some(type_), tokens)
    } else {
        (None, tokens)
    };
    consume!(tokens, TokenKind::Assign, TokenKind::Assign);
    let (expr, tokens) = parse_expr(tokens)?;
    Ok((
        Statement::Assignment(Assignment {
            type_,
            left: name.clone(),
            right: expr,
        }),
        tokens,
    ))
}

fn parse_record_expr(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    let (t, tokens) = parse_type_expr(tokens)?;
    consume!(tokens, TokenKind::Lbrac, TokenKind::Lbrac);
    let (fields, tokens) = parse_record_expr_tail(tokens)?;
    let e = Expr::Record(RecordExpr {
        t,
        fields,
        actual: Rc::new(RefCell::new(None)),
    });
    Ok((e, tokens))
}

fn parse_record_expr_tail(tokens: &[Token]) -> Result<(HashMap<String, Expr>, &[Token])> {
    consume!(
        tokens,
        TokenKind::Symbol(first_name),
        TokenKind::Symbol("field_name".into())
    );
    consume!(tokens, TokenKind::Assign, TokenKind::Assign);
    let (first_val, mut tokens) = parse_expr(tokens)?;

    let mut fields = HashMap::new();
    fields.insert(first_name.clone(), first_val);
    while consume!(tokens, TokenKind::Rbrac).is_none() {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        consume!(
            rest,
            TokenKind::Symbol(name),
            TokenKind::Symbol("field_name".into())
        );
        consume!(rest, TokenKind::Assign, TokenKind::Assign);
        let (e, rest) = parse_expr(rest)?;
        fields.insert(name.clone(), e);
        tokens = rest;
    }

    consume!(tokens, TokenKind::Rbrac, TokenKind::Rbrac);
    Ok((fields, tokens))
}

fn parse_expr(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    fn parse_symbol(tokens: &[Token]) -> Result<(Expr, &[Token])> {
        consume!(
            tokens,
            TokenKind::Symbol(name),
            TokenKind::Symbol("".to_string())
        );
        Ok((Expr::Symbol(name.clone()), tokens))
    }

    fn parse_forall_expr(tokens: &[Token]) -> Result<(Expr, &[Token])> {
        let (f, rest) = parse_forall(tokens, parse_expr)?;
        Ok((Expr::Forall(f), rest))
    }

    let (expr, rest) = match tokens {
        [(TokenKind::Lparen, _), rest @ ..] => {
            let (inner, rest) = parse_expr(rest)?;
            consume!(rest, TokenKind::Rparen, TokenKind::Rparen);
            Ok((inner, rest))
        }
        _ => [
            parse_number,
            parse_bool,
            parse_symbol,
            parse_string,
            parse_forall_expr,
            parse_record_expr,
        ]
        .iter()
        .filter_map(|f| f(tokens).ok())
        .next()
        .ok_or(ParseError::NoRuleMatch {
            expected: "Expression".to_string(),
            remaining: tokens.into(),
        }),
    }?;

    parse_expr_tail(expr, rest)
}

fn parse_expr_tail(expr: Expr, rest: &[Token]) -> Result<(Expr, &[Token])> {
    let mut end_after = true;
    let (e, rest) = if let [(TokenKind::Infix(i), _), rest @ ..] = rest {
        let (right, rest) = parse_expr(rest)?;
        end_after = false;
        (
            Expr::Infix {
                left: Box::new(expr),
                op: i.clone(),
                right: Box::new(right),
                eq_typename_buf: Rc::default(),
            },
            rest,
        )
    } else {
        (expr, rest)
    };

    let (e, rest) = if let [(TokenKind::Lsquare, _), rest @ ..] = rest {
        let (args, rest) = parse_forall_elim(rest)?;
        end_after = false;
        (
            Expr::ForallElim(ForallElim {
                expr: Box::new(e),
                args,
            }),
            rest,
        )
    } else {
        (e, rest)
    };

    let (e, rest) = if let Some((_, rest)) = consume!(rest, TokenKind::Dot) {
        consume!(
            rest,
            TokenKind::Symbol(fieldname),
            TokenKind::Symbol("field_name".into())
        );
        end_after = false;
        (
            Expr::FieldAccess {
                from: Box::new(e),
                offset: Rc::new(RefCell::new(0)),
                fieldname: fieldname.clone(),
            },
            rest,
        )
    } else {
        (e, rest)
    };

    if end_after {
        return Ok((e, rest));
    }

    parse_expr_tail(e, rest)
}

fn parse_string(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    consume!(
        tokens,
        TokenKind::String(s),
        TokenKind::String("".to_string())
    );
    Ok((Expr::String(s.clone()), tokens))
}

fn parse_number(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    match tokens {
        [(TokenKind::Float(n), _), rest @ ..] => Ok((Expr::Float(*n), rest)),
        [(TokenKind::Int(n), _), rest @ ..] => Ok((Expr::Int(*n), rest)),
        other => end_of_match!(other, TokenKind::Float(NAN)),
    }
}
fn parse_bool(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    match tokens {
        [(TokenKind::True, _), rest @ ..] => Ok((Expr::Bool(true), rest)),
        [(TokenKind::False, _), rest @ ..] => Ok((Expr::Bool(false), rest)),
        other => end_of_match!(other, TokenKind::True),
    }
}

fn parse_return(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    consume!(tokens, rest, TokenKind::Return, TokenKind::Return);
    let (value, rest) = parse_expr(rest)?;
    Ok((Statement::Return(value), rest))
}

fn parse_send(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    consume!(tokens, TokenKind::Send, TokenKind::Send);
    consume!(tokens, TokenKind::Lparen, TokenKind::Lparen);
    let (left, tokens) = parse_expr(tokens)?;
    consume!(tokens, TokenKind::Comma, TokenKind::Comma);

    let (right, tokens) = parse_expr(tokens)?;
    consume!(tokens, TokenKind::Rparen, TokenKind::Rparen);
    Ok((
        Statement::Send {
            destination: left,
            value: right,
        },
        tokens,
    ))
}

fn parse_update_intro(tokens: &[Token]) -> Result<(Vec<String>, &[Token])> {
    consume!(tokens, TokenKind::Update, TokenKind::Update);
    match tokens {
        [(TokenKind::Lsquare, _), rest @ ..] => parse_gen_vars(rest),
        rest => Ok((vec![], rest)),
    }
}

fn parse_gen_vars(tokens: &[Token]) -> Result<(Vec<String>, &[Token])> {
    consume!(
        tokens,
        TokenKind::Symbol(e),
        TokenKind::Symbol("_".to_string())
    );
    let mut exprs = vec![e.clone()];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rsquare, _), ..]) {
        let rest = tokens;
        consume!(rest, TokenKind::Comma, TokenKind::Comma);
        consume!(
            rest,
            TokenKind::Symbol(e),
            TokenKind::Symbol("_".to_string())
        );
        tokens = rest;
        exprs.push(e.clone());
    }
    consume!(tokens, TokenKind::Rsquare, TokenKind::Rsquare);

    Ok((exprs, tokens))
}

fn parse_updater(tokens: &[Token]) -> Result<(Update, &[Token])> {
    let (t_vars, tokens) = parse_update_intro(tokens)?;
    consume!(tokens, TokenKind::Lparen, TokenKind::Lparen);
    let (arg, tokens) = parse_symbol(tokens)?;
    consume!(tokens, TokenKind::Colon, TokenKind::Colon);
    let (inp_type, tokens) = parse_type_expr(tokens)?;
    consume!(tokens, TokenKind::Rparen, TokenKind::Rparen);
    let (statements, tokens) = parse_statement_block(tokens)?;
    Ok((
        Update {
            t_vars,
            inp_type,
            inp_name: arg.clone(),
            body: statements,
        },
        tokens,
    ))
}
