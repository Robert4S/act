use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    f64::NAN,
    fmt::Debug,
    rc::Rc,
};

use crate::tokenise::{InfixToken, Token, TokenKind};

use super::typecheck;

macro_rules! consume {
    ($tokens:ident, $p:pat) => {
        match $tokens {
            [(o, _), rest @ ..] if matches!(o, $p) => Some((o, rest)),
            _ => None,
        }
    };
    ($tokens:ident, $p:pat, $err:expr) => {
        let ($p, $tokens) = (match $tokens {
            [(o, _), rest @ ..] if matches!(o, $p) => (o, rest),
            [(o, _), rest @ ..] => return make_error!($err, o.clone(), rest.to_vec().into()),
            _ => return make_error!($err, TokenKind::EOF, Vec::new()),
        }) else {
            unreachable!();
        };
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
    Daemon(Actor),
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
    pub type_: TypeExpr,
    pub right: Expr,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Type;

pub trait ForallT {
    type Kind: Debug + Clone + Eq + PartialEq;

    fn parse_typevar(tokens: &[Token]) -> Result<((String, Self::Kind), &[Token])>;
}

impl ForallT for TypeExpr {
    type Kind = typecheck::Kind;
    fn parse_typevar(tokens: &[Token]) -> Result<((String, Self::Kind), &[Token])> {
        match tokens {
            [(TokenKind::TypeVar(name), _), (TokenKind::Lsquare, _), rest @ ..] => {
                let (arity, rest) = parse_hkt_typevar_tail(rest)?;
                let kind = typecheck::Kind::Function {
                    args: (0..arity).map(|_| typecheck::Kind::Type).collect(),
                    output: Box::new(typecheck::Kind::Type),
                };
                Ok(((name.clone(), kind), rest))
            }
            [(TokenKind::TypeVar(name), _), rest @ ..] => {
                Ok(((name.clone(), typecheck::Kind::Type), rest))
            }
            other => end_of_match!(other, TokenKind::TypeVar("_".to_string())),
        }
    }
}

fn parse_underscore(tokens: &[Token]) -> Result<&[Token]> {
    match tokens {
        [(TokenKind::Symbol(s), _), rest @ ..] if s.as_str() == "_" => Ok(rest),
        other => end_of_match!(other, TokenKind::Symbol(String::from("_"))),
    }
}

fn parse_hkt_typevar_tail(tokens: &[Token]) -> Result<(usize, &[Token])> {
    let mut tokens = parse_underscore(tokens)?;
    if let Some((_, rest)) = consume!(tokens, TokenKind::Rsquare) {
        return Ok((1, rest));
    }
    let mut acc = 1;
    while !matches!(tokens, [(TokenKind::Rsquare, _), ..]) {
        consume!(tokens, rest, TokenKind::Comma, TokenKind::Comma);
        tokens = parse_underscore(rest)?;
        acc += 1;
    }

    consume!(tokens, TokenKind::Rsquare, TokenKind::Rsquare);

    Ok((acc, tokens))
}

impl ForallT for Expr {
    type Kind = Type;

    fn parse_typevar(tokens: &[Token]) -> Result<((String, Self::Kind), &[Token])> {
        match tokens {
            [(TokenKind::TypeVar(name), _), rest @ ..] => Ok(((name.clone(), Type), rest)),
            other => end_of_match!(other, TokenKind::TypeVar("_".to_string())),
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
}

fn parse_forall<T: ForallT>(
    tokens: &[Token],
    parse_t: impl Fn(&[Token]) -> Result<(T, &[Token])>,
) -> Result<(Forall<T>, &[Token])> {
    let rest = match tokens {
        [(TokenKind::Lsquare, _), rest @ ..] => Ok(rest),
        other => end_of_match!(other, TokenKind::Lsquare),
    }?;

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

fn parse_type_expr(tokens: &[Token]) -> Result<(TypeExpr, &[Token])> {
    fn parse_forall_type(tokens: &[Token]) -> Option<(TypeExpr, &[Token])> {
        let (f, rest) = parse_forall(tokens, parse_type_expr).ok()?;
        Some((TypeExpr::Forall(f), rest))
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
    let rest = match tokens {
        [(TokenKind::Forall, _), rest @ ..] => Ok(rest),
        other => end_of_match!(other, TokenKind::Forall),
    }
    .ok()?;

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
    if let [(TokenKind::TypeVar(name), _), rest @ ..] = tokens {
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
    let (name, tokens) = parse_symbol(tokens)?;
    consume!(tokens, TokenKind::Colon, TokenKind::Colon);
    let (type_, tokens) = parse_type_expr(tokens)?;
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
    let (e, rest) = if let [(TokenKind::Infix(i), _), rest @ ..] = rest {
        let (right, rest) = parse_expr(rest)?;
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
        (
            Expr::ForallElim(ForallElim {
                expr: Box::new(e),
                args,
            }),
            rest,
        )
    } else {
        return Ok((e, rest));
    };

    parse_expr_tail(e, rest)
}

fn parse_string(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    match tokens {
        [(TokenKind::String(s), _), rest @ ..] => Ok((Expr::String(s.clone()), rest)),
        other => end_of_match!(other, TokenKind::String("".to_string())),
    }
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
    match tokens {
        [(TokenKind::Return, _), rest @ ..] => {
            let (value, rest) = parse_expr(rest)?;
            Ok((Statement::Return(value), rest))
        }
        other => end_of_match!(other, TokenKind::Return),
    }
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
    match tokens {
        [(TokenKind::Update, _), (TokenKind::Lsquare, _), rest @ ..] => parse_gen_vars(rest),
        [(TokenKind::Update, _), rest @ ..] => Ok((vec![], rest)),
        other => end_of_match!(other, TokenKind::Update),
    }
}

fn parse_gen_vars(tokens: &[Token]) -> Result<(Vec<String>, &[Token])> {
    let (e, tokens) = match tokens {
        [(TokenKind::TypeVar(s), _), rest @ ..] => Ok((s.clone(), rest)),
        other => end_of_match!(other, TokenKind::TypeVar("_".to_string())),
    }?;
    let mut exprs = vec![e];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rsquare, _), ..]) {
        let rest = tokens;
        consume!(rest, TokenKind::Comma, TokenKind::Comma);
        consume!(
            rest,
            TokenKind::TypeVar(e),
            TokenKind::TypeVar("_".to_string())
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
