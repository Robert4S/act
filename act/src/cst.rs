use std::{f32::NAN, fmt::Debug};

use crate::{
    codegen::{self, Instruction, Literal, Value},
    tokenise::{InfixToken, Token, TokenKind},
};
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
                write!(f, "Line {line_num}: Expected {expected:?}, got {got:?}")
            }
            Self::NoRuleMatch {
                expected,
                remaining,
            } => {
                let mut remaining = remaining.clone();
                let line_num = remaining.pop_front().map(|(_, l)| l).unwrap_or(0);
                write!(f, "Line {line_num}: Expected the rule {expected}, but could not match any patterns")
            }
        }
    }
}

type Result<T> = std::result::Result<T, ParseError>;

type Cst = Vector<Actor>;

pub fn gen_instructions(cst: Cst) -> Vec<Instruction> {
    cst.into_iter()
        .map(|a| Statement::Actor(a))
        .map(|s| s.to_instr())
        .collect()
}

#[derive(Debug, Clone)]
pub struct Actor {
    name: String,
    state: State,
    initialiser: Initialiser,
    update: Update,
}

impl Actor {
    fn get_state_name(&self) -> String {
        match &self.state.0 {
            Expr::Symbol(s) => s.clone(),
            _ => panic!("State must be a symbol"),
        }
    }
}

#[derive(Debug, Clone)]
struct Update {
    inp_name: String,
    body: Vector<Statement>,
}

#[derive(Debug, Clone)]
struct State(Expr);

#[derive(Debug, Clone)]
pub struct Initialiser {
    body: Vector<Statement>,
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assignment(Assignment),
    Return(Expr),
    Actor(Actor),
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

impl Statement {
    pub fn to_instr(&self) -> codegen::Instruction {
        match self {
            Statement::Assignment(assignment) => Instruction::Assignment {
                name: assignment.left.clone(),
                value: assignment.right.to_value(),
            },
            Statement::Return(expr) => Instruction::Return(expr.to_value()),
            Statement::Actor(actor) => Instruction::Actor(codegen::Actor {
                name: actor.name.clone(),
                state_name: actor.get_state_name(),
                init: codegen::Init {
                    body: actor
                        .initialiser
                        .body
                        .clone()
                        .into_iter()
                        .map(|s| s.to_instr())
                        .collect::<Vec<Instruction>>(),
                },
                update: codegen::Update {
                    arg: actor.update.inp_name.clone(),
                    body: actor
                        .update
                        .body
                        .clone()
                        .into_iter()
                        .map(|s| s.to_instr())
                        .collect::<Vec<Instruction>>(),
                },
            }),
            Statement::Send { destination, value } => Instruction::Send {
                to: destination.to_value(),
                value: value.to_value(),
            },
            Statement::If {
                condition,
                body,
                otherwise,
            } => Instruction::If {
                cond: condition.to_value(),
                then: body
                    .clone()
                    .into_iter()
                    .map(|s| s.to_instr())
                    .collect::<Vec<Instruction>>(),
                otherwise: otherwise
                    .clone()
                    .map(|body| {
                        body.into_iter()
                            .map(|s| s.to_instr())
                            .collect::<Vec<Instruction>>()
                    })
                    .unwrap_or(vec![]),
            },
        }
    }
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

impl Expr {
    pub fn to_value(&self) -> codegen::Value {
        match self {
            Expr::Number(n) => Value::Literal(Literal::Number(*n)),
            Expr::String(s) => Value::Literal(Literal::String(s.clone())),
            Expr::Symbol(s) => Value::Variable(s.clone()),
            Expr::Bool(b) => Value::Literal(Literal::Bool(*b)),
            Expr::Infix { left, op, right } => {
                infix_to_value(left.clone(), op.clone(), right.clone())
            }
        }
    }
}

fn infix_to_value(left: Box<Expr>, op: InfixToken, right: Box<Expr>) -> codegen::Value {
    let function = match op {
        InfixToken::Plus => "eval_plus",
        InfixToken::Minus => "eval_minus",
        InfixToken::And => "eval_and",
        InfixToken::Or => "eval_or",
        InfixToken::GE => "eval_ge",
        InfixToken::LE => "eval_le",
        InfixToken::Greater => "eval_greater",
        InfixToken::Lesser => "eval_lesser",
        InfixToken::Equal => "eval_eq",
        InfixToken::Mul => "eval_mul",
        InfixToken::Div => "eval_div",
        InfixToken::Assign => panic!("Assigning is not an expression"),
    };

    Value::Call {
        function: function.to_string(),
        args: vec![left.to_value(), right.to_value()],
    }
}

pub fn parse(tokens: &[Token]) -> Result<Cst> {
    let mut tokens = tokens;
    let mut actors = Vec::new();
    while !matches!(tokens, [(TokenKind::EOF, _)]) {
        let (actor, rest) = parse_actor(tokens)?;
        let actor = match actor {
            Statement::Actor(a) => a,
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
    let tokens = match tokens {
        [(TokenKind::Actor, _), rest @ ..] => Ok(rest),
        other => end_of_match!(other, TokenKind::Actor),
    }?;
    let (name, tokens) = parse_symbol(tokens)?;
    let (_, tokens) = parse_lbrac(tokens)?;
    let (state, tokens) = parse_state(tokens)?;
    let (initialiser, tokens) = parse_initialiser(tokens)?;
    let (update, tokens) = parse_updater(tokens)?;
    let (_, tokens) = parse_rbrac(tokens)?;
    Ok((
        Statement::Actor(Actor {
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

fn parse_statement_block(tokens: &[Token]) -> Result<(Vector<Statement>, &[Token])> {
    let (_, tokens) = parse_lbrac(tokens)?;
    let mut statements = Vec::new();
    let mut input = tokens;
    while let (statement, [(TokenKind::Semi, _), rest @ ..]) = parse_statement(input)? {
        statements.push(statement);
        input = rest;
        if let Ok(_) = parse_rbrac(input) {
            break;
        }
    }

    let (_, input) = parse_rbrac(input)?;
    let statements = statements.into_iter().collect();
    Ok((statements, input))
}

fn parse_statement(tokens: &[Token]) -> Result<(Statement, &[Token])> {
    let fns = vec![
        parse_assignment,
        parse_actor,
        parse_return,
        parse_send,
        parse_if,
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
            let (_, tokens) = parse_lbrac(tokens)?;
            let mut statements = Vec::new();
            let mut tokens = tokens;
            while let (statement, [(TokenKind::Semi, _), rest @ ..]) = parse_statement(tokens)? {
                statements.push(statement);
                tokens = rest;
                if let Ok(_) = parse_rbrac(tokens) {
                    break;
                }
            }
            let (_, tokens) = parse_rbrac(tokens)?;
            let statements = statements.into_iter().collect::<Vector<Statement>>();
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
