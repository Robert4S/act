use std::{collections::VecDeque, fmt::Display};

pub type Token = (TokenKind, usize);

#[derive(Debug, Clone)]
pub enum TokenKind {
    // Characters
    Lbrac,
    Rbrac,
    Lparen,
    Rparen,
    Comma,
    Semi,
    Colon,
    Dot,
    Lsquare,
    Rsquare,
    Assign,

    // Keywords
    Not,
    Actor,
    Initialiser,
    Update,
    True,
    False,
    Return,
    Send,
    State,
    If,
    Else,
    Daemon,
    Intrinsic,
    Forall,
    Type,
    NewType,
    Let,

    // Rules
    Infix(InfixToken),
    Float(f64),
    Int(i64),
    Symbol(String),
    String(String),
    TypeName(String),

    // EOF
    EOF,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InfixToken {
    Plus,
    PlusFloat,
    Minus,
    MinusFloat,
    Mod,
    Mul,
    MulFloat,
    Div,
    DivFloat,
    GE,
    GEFloat,
    LE,
    LEFloat,
    Greater,
    GreaterFloat,
    Lesser,
    LesserFloat,
    And,
    Or,
    Equal,
}

impl Display for InfixToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol = match self {
            InfixToken::Plus => "+",
            InfixToken::PlusFloat => "+.",
            InfixToken::Minus => "-",
            InfixToken::MinusFloat => "-.",
            InfixToken::Mod => "%",
            InfixToken::Mul => "*",
            InfixToken::MulFloat => "*.",
            InfixToken::Div => "/",
            InfixToken::DivFloat => "/.",
            InfixToken::GE => ">=",
            InfixToken::GEFloat => ">=.",
            InfixToken::LE => "<=",
            InfixToken::LEFloat => "<=.",
            InfixToken::Greater => ">",
            InfixToken::GreaterFloat => ">.",
            InfixToken::Lesser => "<",
            InfixToken::LesserFloat => "<.",
            InfixToken::And => "&&",
            InfixToken::Or => "||",
            InfixToken::Equal => "==",
        };
        write!(f, "{}", symbol)
    }
}

pub fn tokenize_all<'a>(input: &'a [char]) -> Option<Vec<Token>> {
    let mut line_num = 1;
    let mut tokens = vec![];
    let mut input = input.to_vec();
    while !input.is_empty() {
        let (token, rest) = tokenize(input.as_slice(), line_num)?;
        line_num = token.1;
        tokens.push(token);
        input = rest;
    }
    let tokens = tokens.into_iter().map(update_keyword).collect::<Vec<_>>();
    Some(tokens)
}

pub fn tokenize<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    match input {
        // Characters
        ['(', rest @ ..] => Some(((TokenKind::Lparen, line_number), rest.to_owned())),
        [')', rest @ ..] => Some(((TokenKind::Rparen, line_number), rest.to_owned())),
        ['∀', rest @ ..] => Some(((TokenKind::Forall, line_number), rest.to_owned())),
        ['=', rest @ ..] if rest.first().map(|c| *c != '=').unwrap_or(true) => {
            Some(((TokenKind::Assign, line_number), rest.to_owned()))
        }
        ['{', rest @ ..] => Some(((TokenKind::Lbrac, line_number), rest.to_owned())),
        ['}', rest @ ..] => Some(((TokenKind::Rbrac, line_number), rest.to_owned())),
        [',', rest @ ..] => Some(((TokenKind::Comma, line_number), rest.to_owned())),
        [';', rest @ ..] => Some(((TokenKind::Semi, line_number), rest.to_owned())),
        [':', rest @ ..] => Some(((TokenKind::Colon, line_number), rest.to_owned())),
        ['.', rest @ ..] => Some(((TokenKind::Dot, line_number), rest.to_owned())),
        ['[', rest @ ..] => Some(((TokenKind::Lsquare, line_number), rest.to_owned())),
        [']', rest @ ..] => Some(((TokenKind::Rsquare, line_number), rest.to_owned())),
        ['#', rest @ ..] => {
            let mut toks = rest;
            loop {
                match toks {
                    ['\n', ..] => break,
                    [_, rest @ ..] => toks = rest,
                    _ => break,
                }
            }
            tokenize(toks, line_number)
        }

        // Lookahead rules
        ['"', rest @ ..] => tokenise_string(rest, line_number),
        ['\n', rest @ ..] => tokenize(rest, line_number + 1),
        [c, rest @ ..] if c.is_whitespace() => tokenize(rest, line_number),

        // EOF
        [] => Some(((TokenKind::EOF, line_number), vec![])),

        // Backtracking rules
        other => vec![
            tokenise_number,
            tokenise_infix,
            tokenise_symbol,
            tokenise_typename,
            tokenise_string,
        ]
        .iter()
        .filter_map(|f| f(other, line_number))
        .next(),
    }
}

fn tokenise_infix<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    match input {
        ['>', '=', '.', rest @ ..] => Some((InfixToken::GEFloat, rest)),
        ['<', '=', '.', rest @ ..] => Some((InfixToken::LEFloat, rest)),
        ['=', '=', rest @ ..] => Some((InfixToken::Equal, rest)),
        ['>', '=', rest @ ..] => Some((InfixToken::GE, rest)),
        ['<', '=', rest @ ..] => Some((InfixToken::LE, rest)),
        ['&', '&', rest @ ..] => Some((InfixToken::And, rest)),
        ['|', '|', rest @ ..] => Some((InfixToken::Or, rest)),
        ['+', '.', rest @ ..] => Some((InfixToken::PlusFloat, rest)),
        ['-', '.', rest @ ..] => Some((InfixToken::MinusFloat, rest)),
        ['*', '.', rest @ ..] => Some((InfixToken::MulFloat, rest)),
        ['/', '.', rest @ ..] => Some((InfixToken::DivFloat, rest)),
        ['>', '.', rest @ ..] => Some((InfixToken::GreaterFloat, rest)),
        ['<', '.', rest @ ..] => Some((InfixToken::LesserFloat, rest)),
        ['>', rest @ ..] => Some((InfixToken::Greater, rest)),
        ['<', rest @ ..] => Some((InfixToken::Lesser, rest)),
        ['+', rest @ ..] => Some((InfixToken::Plus, rest)),
        ['*', rest @ ..] => Some((InfixToken::Mul, rest)),
        ['-', rest @ ..] => Some((InfixToken::Minus, rest)),
        ['/', rest @ ..] => Some((InfixToken::Div, rest)),
        ['%', rest @ ..] => Some((InfixToken::Mod, rest)),
        _ => None,
    }
    .map(|(t, r)| ((TokenKind::Infix(t), line_number), r.to_owned()))
}

fn tokenise_number<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    let mut input = input;
    let mut left = "".to_string();
    let mut right = "".to_string();

    match input {
        ['-', rest @ ..] => {
            input = rest;
            left.push('-');
        }
        _ => (),
    }

    while let [c, rest @ ..] = input {
        if !c.is_numeric() {
            break;
        }
        left.push(*c);
        input = rest;
    }

    match input {
        ['.', rest @ ..] => {
            input = rest;
            while let [c, rest @ ..] = input {
                if !c.is_numeric() {
                    break;
                }
                right.push(*c);
                input = rest;
            }
        }
        _ => (),
    }

    if right.is_empty() {
        let n = left.parse::<i64>().ok()?;
        return Some(((TokenKind::Int(n), line_number), input.to_vec()));
    }

    left.push('.');
    left.push_str(&right);

    let n = left.parse::<f64>().ok()?;
    Some(((TokenKind::Float(n), line_number), input.to_vec()))
}

fn tokenise_typename<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    let mut s = match input {
        [c, ..] if c.is_lowercase() => return None,
        _ => "".to_string(),
    };
    let mut input = input;
    let cannot_contain = "{}\"(),;.:[]".chars().collect::<Vec<char>>();
    let cannot_contain = cannot_contain.as_slice();

    while let [c, rest @ ..] = input {
        if cannot_contain.contains(c) || c.is_whitespace() {
            let mut rest: VecDeque<_> = rest.iter().cloned().collect();
            rest.push_front(*c);
            return Some((
                (TokenKind::TypeName(s), line_number),
                rest.into_iter().collect(),
            ));
        }
        s.push(*c);
        input = rest;
    }
    None
}

fn tokenise_symbol<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    let mut s = match input {
        [c, ..] if c.is_uppercase() => return None,
        _ => "".to_string(),
    };
    let mut input = input;
    let cannot_contain = "{}\"(),;.:[]&|!+-=*/\\".chars().collect::<Vec<char>>();
    let cannot_contain = cannot_contain.as_slice();

    while let [c, rest @ ..] = input {
        if cannot_contain.contains(c) || c.is_whitespace() {
            let mut rest: VecDeque<_> = rest.iter().cloned().collect();
            rest.push_front(*c);
            return Some((
                (TokenKind::Symbol(s), line_number),
                rest.into_iter().collect(),
            ));
        }
        s.push(*c);
        input = rest;
    }
    None
}

fn tokenise_string<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    let mut input = input;
    let mut s = "".to_string();
    let mut escaped = false;

    while let [c, rest @ ..] = input {
        if escaped {
            match c {
                'n' => s.push('\n'),
                't' => s.push('\t'),
                'r' => s.push('\r'),
                '\\' => s.push('\\'),
                '"' => s.push('"'),
                other => s.push(*other), // Handle unknown escape sequences as literal characters
            }
            escaped = false;
            input = rest;
        } else if *c == '"' {
            return Some(((TokenKind::String(s), line_number), rest.to_vec()));
        } else if *c == '\\' {
            escaped = true;
            input = rest
        } else {
            s.push(*c);
            input = rest;
        }
    }
    None
}

fn update_keyword(token: Token) -> Token {
    match token {
        (TokenKind::Symbol(s), n) => (
            match s.as_str() {
                "actor" => TokenKind::Actor,
                "daemon" => TokenKind::Daemon,
                "type" => TokenKind::Type,
                "newtype" => TokenKind::NewType,
                "send" => TokenKind::Send,
                "for" => TokenKind::Forall,
                "return" => TokenKind::Return,
                "false" => TokenKind::False,
                "true" => TokenKind::True,
                "initialiser" => TokenKind::Initialiser,
                "update" => TokenKind::Update,
                "not" => TokenKind::Not,
                "state" => TokenKind::State,
                "if" => TokenKind::If,
                "else" => TokenKind::Else,
                "intrinsic" => TokenKind::Intrinsic,
                "let" => TokenKind::Let,
                _ => TokenKind::Symbol(s),
            },
            n,
        ),
        _ => token,
    }
}
