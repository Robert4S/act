use im::Vector;

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

    // Rules
    Infix(InfixToken),
    Number(f32),
    Symbol(String),
    String(String),

    // EOF
    EOF,
}

#[derive(Debug, Clone)]
pub enum InfixToken {
    Plus,
    Minus,
    And,
    Or,
    GE,
    LE,
    Greater,
    Lesser,
    Equal,
    Mul,
    Div,
    Assign,
}

pub fn tokenize_all<'a>(input: &'a [char]) -> Option<Vec<Token>> {
    let mut line_num = 0;
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
        ['{', rest @ ..] => Some(((TokenKind::Lbrac, line_number), rest.to_owned())),
        ['}', rest @ ..] => Some(((TokenKind::Rbrac, line_number), rest.to_owned())),
        [',', rest @ ..] => Some(((TokenKind::Comma, line_number), rest.to_owned())),
        [';', rest @ ..] => Some(((TokenKind::Semi, line_number), rest.to_owned())),

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
            tokenise_string,
        ]
        .iter()
        .filter_map(|f| f(other, line_number))
        .next(),
    }
}

fn tokenise_infix<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    match input {
        ['=', '=', rest @ ..] => Some((InfixToken::Equal, rest)),
        ['>', '=', rest @ ..] => Some((InfixToken::GE, rest)),
        ['<', '=', rest @ ..] => Some((InfixToken::LE, rest)),
        ['&', '&', rest @ ..] => Some((InfixToken::And, rest)),
        ['|', '|', rest @ ..] => Some((InfixToken::Or, rest)),
        ['>', rest @ ..] => Some((InfixToken::Greater, rest)),
        ['<', rest @ ..] => Some((InfixToken::Lesser, rest)),
        ['+', rest @ ..] => Some((InfixToken::Plus, rest)),
        ['*', rest @ ..] => Some((InfixToken::Mul, rest)),
        ['-', rest @ ..] => Some((InfixToken::Minus, rest)),
        ['/', rest @ ..] => Some((InfixToken::Div, rest)),
        ['=', rest @ ..] => Some((InfixToken::Assign, rest)),
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

    left.push('.');
    left.push_str(&right);

    let n = left.parse::<f32>().ok()?;
    Some(((TokenKind::Number(n), line_number), input.to_vec()))
}

fn tokenise_symbol<'a>(input: &'a [char], line_number: usize) -> Option<(Token, Vec<char>)> {
    let mut input = input;
    let mut s = "".to_string();
    let cannot_contain = "{}\"(),;".chars().collect::<Vec<char>>();
    let cannot_contain = cannot_contain.as_slice();

    while let [c, rest @ ..] = input {
        if cannot_contain.contains(c) || c.is_whitespace() {
            let mut rest: Vector<_> = rest.into();
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
                "Actor" => TokenKind::Actor,
                "Daemon" => TokenKind::Daemon,
                "send" => TokenKind::Send,
                "return" => TokenKind::Return,
                "false" => TokenKind::False,
                "true" => TokenKind::True,
                "Initialiser" => TokenKind::Initialiser,
                "Update" => TokenKind::Update,
                "not" => TokenKind::Not,
                "State" => TokenKind::State,
                "if" => TokenKind::If,
                "else" => TokenKind::Else,
                "intrinsic" => TokenKind::Intrinsic,
                _ => TokenKind::Symbol(s),
            },
            n,
        ),
        _ => token,
    }
}
