use std::{f32::NAN, fmt::Debug};

use crate::tokenise::{InfixToken, Token, TokenKind};
use im::Vector;

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
            _ => make_error!($expected, TokenKind::EOF, Vector::new()),
        }
    };
}

pub enum ParseError {
    WrongToken {
        expected: TokenKind,
        got: TokenKind,
        remaining: Vector<Token>,
    },
    NoRuleMatch {
        expected: String,
        remaining: Vector<Token>,
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
                let mut remaining = remaining.clone();
                let line_num = remaining.pop_front().map(|(_, l)| l).unwrap_or(0);
                write!(
                    f,
                    "Line {line_num}: Expected TOKEN({expected:?}), got TOKEN({got:?})"
                )
            }
            Self::NoRuleMatch {
                expected,
                remaining,
            } => {
                let mut remaining = remaining.clone();
                let line_num = remaining.pop_front().map(|(_, l)| l).unwrap_or(0);
                write!(
                    f,
                    "Line {line_num}: Expected RULE({expected}), but could not match any patterns"
                )
            }
        }
    }
}

type Result<T> = std::result::Result<T, ParseError>;

pub type Cst = Vector<ActorKind>;

#[derive(Debug, Clone)]
pub enum ActorKind {
    Daemon(Actor),
    Actor(Actor),
}

#[derive(Debug, Clone)]
pub struct Actor {
    pub name: String,
    pub state: State,
    pub initialiser: Initialiser,
    pub update: Update,
}

impl Actor {
    pub fn get_state_name(&self) -> String {
        match &self.state.0 {
            Expr::Symbol(s) => s.clone(),
            _ => panic!("State must be a symbol"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Update {
    pub inp_name: String,
    pub body: Vector<Statement>,
}

#[derive(Debug, Clone)]
pub struct State(Expr);

#[derive(Debug, Clone)]
pub struct Initialiser {
    pub body: Vector<Statement>,
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
        body: Vector<Statement>,
        otherwise: Option<Vector<Statement>>,
    },
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub left: String,
    pub right: Expr,
}

#[derive(Debug, Clone)]
pub enum Expr {
    Number(f32),
    String(String),
    Symbol(String),
    Bool(bool),
    Infix {
        left: Box<Expr>,
        op: InfixToken,
        right: Box<Expr>,
    },
}

pub fn parse(tokens: &[Token]) -> Result<Cst> {
    let mut tokens = tokens;
    let mut actors = Vec::new();
    while !matches!(tokens, [(TokenKind::EOF, _)]) {
        let (actor, rest) = parse_actor(tokens)?;
        let actor = match actor {
            Statement::Actor(a) => ActorKind::Actor(a),
            Statement::Daemon(a) => ActorKind::Daemon(a),
            o => panic!("nonono {o:?} is not an actor"),
        };
        actors.push(actor);
        tokens = rest;
    }
    Ok(actors.into())
}

fn parse_symbol(tokens: &[Token]) -> Result<(String, &[Token])> {
    match tokens {
        [(TokenKind::Symbol(s), _), rest @ ..] => Ok((s.clone(), rest)),
        other => end_of_match!(other, TokenKind::Symbol("".to_string())),
    }
}

fn parse_actor(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let mut kind: Option<Box<dyn Fn(Actor) -> Statement>> = None;
    let tokens = match tokens {
        [(TokenKind::Actor, _), rest @ ..] => {
            kind = Some(Box::new(|a| Statement::Actor(a)));
            Ok(rest)
        }
        [(TokenKind::Daemon, _), rest @ ..] => {
            kind = Some(Box::new(|a| Statement::Daemon(a)));
            Ok(rest)
        }
        other => end_of_match!(other, TokenKind::Actor),
    }?;
    let (name, tokens) = parse_symbol(tokens)?;
    let (_, tokens) = parse_lbrac(tokens)?;
    let (state, tokens) = parse_state(tokens)?;
    let (initialiser, tokens) = parse_initialiser(tokens)?;
    let (update, tokens) = parse_updater(tokens)?;
    let (_, tokens) = parse_rbrac(tokens)?;
    Ok((
        kind.unwrap()(Actor {
            name,
            state: State(state),
            update,
            initialiser,
        }),
        tokens,
    ))
}

fn parse_lbrac(tokens: &[Token]) -> Result<((), &[Token])> {
    match tokens {
        [(TokenKind::Lbrac, _), rest @ ..] => Ok(((), rest)),
        other => end_of_match!(other, TokenKind::Lbrac),
    }
}

fn parse_rbrac(tokens: &[Token]) -> Result<((), &[Token])> {
    match tokens {
        [(TokenKind::Rbrac, _), rest @ ..] => Ok(((), rest)),
        other => end_of_match!(other, TokenKind::Rbrac),
    }
}

fn parse_lparen(tokens: &[Token]) -> Result<((), &[Token])> {
    match tokens {
        [(TokenKind::Lparen, _), rest @ ..] => Ok(((), rest)),
        other => end_of_match!(other, TokenKind::Lparen),
    }
}

fn parse_rparen(tokens: &[Token]) -> Result<((), &[Token])> {
    match tokens {
        [(TokenKind::Rparen, _), rest @ ..] => Ok(((), rest)),
        other => end_of_match!(other, TokenKind::Rparen),
    }
}

fn parse_state(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    match tokens {
        [(TokenKind::State, _), rest @ ..] => match parse_expr(rest)? {
            (state, [(TokenKind::Semi, _), rest @ ..]) => Ok((state, rest)),
            (_, other) => end_of_match!(other, TokenKind::Semi),
        },
        other => end_of_match!(other, TokenKind::State),
    }
}

fn parse_initialiser(tokens: &[Token]) -> Result<(Initialiser, &[Token])> {
    match tokens {
        [(TokenKind::Initialiser, _), rest @ ..] => {
            let (statements, rest) = parse_statement_block(rest)?;
            let initialiser = Initialiser { body: statements };
            Ok((initialiser, rest))
        }
        other => end_of_match!(other, TokenKind::Initialiser),
    }
}

fn parse_semi(tokens: &[Token]) -> Result<&[Token]> {
    match tokens {
        [(TokenKind::Semi, _), rest @ ..] => Ok(rest),
        other => end_of_match!(other, TokenKind::Semi),
    }
}

fn parse_statement_block(tokens: &[Token]) -> Result<(Vector<Statement>, &[Token])> {
    let (_, tokens) = parse_lbrac(tokens)?;
    let mut statements = Vec::new();
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rbrac, _), ..]) {
        let (statement, rest) = parse_statement(tokens)?;
        let rest = parse_semi(rest)?;
        statements.push(statement);
        tokens = rest;
    }
    let (_, tokens) = parse_rbrac(tokens)?;

    let statements = statements.into_iter().collect();
    Ok((statements, tokens))
}

fn parse_statement(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let fns = vec![
        parse_assignment,
        parse_actor,
        parse_return,
        parse_send,
        parse_if,
        parse_intrinsic,
    ];

    fns.iter()
        .filter_map(|f| f(tokens).ok())
        .next()
        .ok_or(ParseError::NoRuleMatch {
            expected: "Statement".to_string(),
            remaining: tokens.into(),
        })
}

fn parse_if(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let (_, tokens) = parse_if_literal(tokens)?;
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

fn parse_else(tokens: &[Token]) -> Result<(Option<Vector<Statement>>, &[Token])> {
    match tokens {
        [(TokenKind::Else, _), rest @ ..] => {
            let (statements, tokens) = parse_statement_block(rest)?;
            Ok((Some(statements), tokens))
        }
        _ => Ok((None, tokens)),
    }
}

fn parse_if_literal(tokens: &[Token]) -> Result<((), &[Token])> {
    match tokens {
        [(TokenKind::If, _), rest @ ..] => Ok(((), rest)),
        other => end_of_match!(other, TokenKind::If),
    }
}

fn parse_intrinsic(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let tokens = parse_intrinsic_literal(tokens)?;
    let (_, tokens) = parse_lparen(tokens)?;
    let (func_name, tokens) = parse_symbol(tokens)?;
    let (_, tokens) = parse_comma(tokens)?;
    let (args, tokens) = parse_intrinsic_tail(tokens)?;

    Ok((Statement::Intrinsic { func_name, args }, tokens))
}

fn parse_intrinsic_tail(tokens: &[Token]) -> Result<(Vec<Expr>, &[Token])> {
    let (e, tokens) = parse_expr(tokens)?;
    let mut exprs = vec![e];
    let mut tokens = tokens;
    while !matches!(tokens, [(TokenKind::Rparen, _), ..]) {
        let (_, rest) = parse_comma(tokens)?;
        let (e, rest) = parse_expr(rest)?;
        tokens = rest;
        exprs.push(e);
    }
    let (_, tokens) = parse_rparen(tokens)?;

    Ok((exprs, tokens))
}

fn parse_intrinsic_literal(tokens: &[Token]) -> Result<&[Token]> {
    match tokens {
        [(TokenKind::Intrinsic, _), rest @ ..] => Ok(rest),
        other => end_of_match!(other, TokenKind::Intrinsic),
    }
}

fn parse_assignment(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let (name, tokens) = parse_symbol(tokens)?;
    match tokens {
        [(TokenKind::Infix(InfixToken::Assign), _), tokens @ ..] => {
            let (expr, tokens) = parse_expr(tokens)?;
            Ok((
                Statement::Assignment(Assignment {
                    left: name.clone(),
                    right: expr,
                }),
                tokens,
            ))
        }
        other => end_of_match!(other, TokenKind::Infix(InfixToken::Assign)),
    }
}

fn parse_expr(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    fn parse_symbol(tokens: &[Token]) -> Result<(Expr, &[Token])> {
        match tokens {
            [(TokenKind::Symbol(name), _), rest @ ..] => Ok((Expr::Symbol(name.clone()), rest)),
            other => end_of_match!(other, TokenKind::Symbol("".to_string())),
        }
    }

    let (expr, rest) = match tokens {
        [(TokenKind::Lparen, _), rest @ ..] => match parse_expr(rest)? {
            (inner, [(TokenKind::Rparen, _), rest @ ..]) => Ok((inner, rest)),
            (_, other) => end_of_match!(other, TokenKind::Rparen),
        },
        _ => vec![parse_number, parse_bool, parse_symbol, parse_string]
            .iter()
            .filter_map(|f| f(tokens).ok())
            .next()
            .ok_or(ParseError::NoRuleMatch {
                expected: "Expression".to_string(),
                remaining: tokens.into(),
            }),
    }?;

    if let [(TokenKind::Infix(i), _), rest @ ..] = rest {
        let (right, rest) = parse_expr(rest)?;
        Ok((
            Expr::Infix {
                left: Box::new(expr),
                op: i.clone(),
                right: Box::new(right),
            },
            rest,
        ))
    } else {
        Ok((expr, rest))
    }
}

fn parse_string(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    match tokens {
        [(TokenKind::String(s), _), rest @ ..] => Ok((Expr::String(s.clone()), rest)),
        other => end_of_match!(other, TokenKind::String("".to_string())),
    }
}

fn parse_number(tokens: &[Token]) -> Result<(Expr, &[Token])> {
    match tokens {
        [(TokenKind::Number(n), _), rest @ ..] => Ok((Expr::Number(*n), rest)),
        other => end_of_match!(other, TokenKind::Number(NAN)),
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
    match tokens {
        [(TokenKind::Send, _), tokens @ ..] => {
            let (_, tokens) = parse_lparen(tokens)?;
            let (left, tokens) = parse_expr(tokens)?;
            let (_, tokens) = parse_comma(tokens)?;
            let (right, tokens) = parse_expr(tokens)?;
            let (_, tokens) = parse_rparen(tokens)?;
            Ok((
                Statement::Send {
                    destination: left,
                    value: right,
                },
                tokens,
            ))
        }
        other => end_of_match!(other, TokenKind::Send),
    }
}

fn parse_comma(tokens: &[Token]) -> Result<((), &[Token])> {
    match tokens {
        [(TokenKind::Comma, _), rest @ ..] => Ok(((), rest)),
        other => end_of_match!(other, TokenKind::Comma),
    }
}

fn parse_updater(tokens: &[Token]) -> Result<(Update, &[Token])> {
    match tokens {
        [(TokenKind::Update, _), tokens @ ..] => {
            let (_, tokens) = parse_lparen(tokens)?;
            let (arg, tokens) = parse_symbol(tokens)?;
            let (_, tokens) = parse_rparen(tokens)?;
            let (statements, tokens) = parse_statement_block(tokens)?;
            Ok((
                Update {
                    inp_name: arg.clone(),
                    body: statements,
                },
                tokens,
            ))
        }
        other => end_of_match!(other, TokenKind::Update),
    }
}
