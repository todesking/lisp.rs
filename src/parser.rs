use crate::value::Value;

use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    Unexpected(String),
    Redundant(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        fmt.write_fmt(format_args!("{:?}", self))
    }
}

impl std::error::Error for ParseError {}

impl std::str::FromStr for Value {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = Parser::new();
        p.parse(s)
    }
}

type ParseResult<'a> = Result<(Value, &'a str), ParseError>;

pub struct Parser {
    names: std::collections::HashMap<Box<str>, Rc<str>>,
}

impl Parser {
    pub fn new() -> Parser {
        Parser {
            names: std::collections::HashMap::new(),
        }
    }
    pub fn parse(&mut self, s: &str) -> Result<Value, ParseError> {
        let s = skip_ws(s);
        parse_expr(self, s).and_then(|(v, s)| {
            let s = skip_ws(s);
            if s.is_empty() {
                Ok(v)
            } else {
                Err(ParseError::Redundant(s.to_owned()))
            }
        })
    }
    pub fn parse_all(&mut self, s: &str) -> Result<Vec<Value>, ParseError> {
        let mut s = skip_ws(s);
        let mut exprs = Vec::new();
        loop {
            if s.is_empty() {
                break;
            }
            let (expr, s1) = parse_expr(self, s)?;
            s = s1;
            exprs.push(expr);
            s = skip_ws(s);
        }
        Ok(exprs)
    }
    pub fn str_intern(&mut self, name: &str) -> Rc<str> {
        self.names
            .get(name)
            .cloned()
            .unwrap_or_else(|| Rc::from(name))
    }
    pub fn new_sym(&mut self, name: &str) -> Value {
        Value::Sym(self.str_intern(name))
    }
}

impl Default for Parser {
    fn default() -> Self {
        Parser::new()
    }
}

fn many(s: &str, mut f: impl FnMut(char) -> bool) -> (&str, &str) {
    s.char_indices()
        .take_while(|(_, c)| f(*c))
        .last()
        .map(|(i, _)| s.split_at(i + 1))
        .unwrap_or(("", s))
}

fn skip_ws(s: &str) -> &str {
    many(s, |c| c == ' ' || c == '\n').1
}

fn consume<'a>(s: &'a str, pat: &str) -> Result<&'a str, ParseError> {
    s.strip_prefix(pat)
        .ok_or_else(|| ParseError::Unexpected(s.to_owned()))
}

fn try_consume<'a>(s: &'a str, pat: &str) -> (bool, &'a str) {
    s.strip_prefix(pat).map(|s| (true, s)).unwrap_or((false, s))
}

fn parse_expr<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    parse_quote(p, s)
        .or_else(|_| parse_num(s))
        .or_else(|_| parse_list(p, s))
        .or_else(|_| parse_symbol(p, s))
}

fn parse_quote<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let s = consume(s, "'")?;
    let (e, s) = parse_expr(p, s)?;
    let e = Value::cons(p.new_sym("quote"), Value::cons(e, Value::nil()));
    Ok((e, s))
}

fn parse_num(s: &str) -> ParseResult {
    let (minus, s) = try_consume(s, "-");
    let (s1, s2) = many(s, |c| '0' <= c && c <= '9');
    if s1.is_empty() {
        Err(ParseError::Unexpected(s2.to_owned()))
    } else {
        let n: i32 = s1.parse().expect("should not reach here");
        let n = if minus { -n } else { n };
        let n = Value::Int(n);
        Ok((n, s2))
    }
}

fn parse_symbol<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let (s1, s2) = many(
        s,
        |c| matches!( c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '+' | '-' | '*' | '/' | '%' | '?' | '!' | '\''),
    );
    match s1 {
        "" => Err(ParseError::Unexpected(s2.to_owned())),
        "'" => Err(ParseError::Unexpected(s2.to_owned())),
        name => Ok((p.new_sym(name), s2)),
    }
}

fn parse_list<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let s = consume(s, "(")?;
    let s = skip_ws(s);

    let mut items = Vec::new();
    let mut s = s;
    while let Ok((e, s1)) = parse_expr(p, s) {
        items.push(e);
        s = skip_ws(s1);
    }

    let (tail, s) = if let Ok(s) = consume(s, ".") {
        let s = skip_ws(s);
        let (e, s) = parse_expr(p, s)?;
        let s = skip_ws(s);
        (e, s)
    } else {
        (Value::Nil, s)
    };

    let s = consume(s, ")")?;
    let e = items.into_iter().rev().fold(tail, |a, x| Value::cons(x, a));

    Ok((e, s))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_num() {
        let e = "1".parse();
        assert_eq!(e, Ok(Value::Int(1)));

        let e = "123".parse();
        assert_eq!(e, Ok(Value::Int(123)));

        let e = "   123".parse();
        assert_eq!(e, Ok(Value::Int(123)));

        let e = "123    ".parse();
        assert_eq!(e, Ok(Value::Int(123)));

        let e: Result<Value, ParseError> = "123a".parse();
        assert_eq!(e, Err(ParseError::Redundant("a".to_owned())));

        let e = "-123".parse();
        assert_eq!(e, Ok(Value::int(-123)));
    }

    #[test]
    fn test_symbol() {
        let e = "a".parse();
        assert_eq!(e, Ok(Value::sym("a")));

        let e = "LONG-symbol'name?!?!".parse();
        assert_eq!(e, Ok(Value::sym("LONG-symbol'name?!?!")));

        let e = "f0".parse();
        assert_eq!(e, Ok(Value::sym("f0")));

        let e = "+-*/%".parse();
        assert_eq!(e, Ok(Value::sym("+-*/%")));
    }

    #[test]
    fn test_quote() {
        let e = "'".parse::<Value>();
        assert_eq!(e, Err(ParseError::Unexpected("".to_owned())));

        let e = "' 1".parse::<Value>();
        assert_eq!(e, Err(ParseError::Unexpected(" 1".to_owned())));

        let e = "'1".parse::<Value>();
        assert_eq!(
            e,
            Ok(Value::cons(
                Value::sym("quote"),
                Value::cons(Value::Int(1), Value::Nil)
            ))
        );

        let e = "'()".parse::<Value>();
        assert_eq!(
            e,
            Ok(Value::cons(
                Value::sym("quote"),
                Value::cons(Value::Nil, Value::Nil)
            ))
        );
    }

    #[test]
    fn test_cons() {
        let e = "(1.2)".parse();
        assert_eq!(e, Ok(Value::cons(Value::Int(1), Value::Int(2))));

        let e = "(  3 . 4  )".parse();
        assert_eq!(e, Ok(Value::cons(Value::Int(3), Value::Int(4))));
    }

    #[test]
    fn test_list() {
        let e = "()".parse();
        assert_eq!(e, Ok(Value::Nil));

        let e = "(1 2 3)".parse();
        assert_eq!(
            e,
            Ok(Value::cons(
                Value::Int(1),
                Value::cons(Value::Int(2), Value::cons(Value::Int(3), Value::Nil))
            ))
        );

        let e = "(1 2 . 3)".parse();
        assert_eq!(
            e,
            Ok(Value::cons(
                Value::Int(1),
                Value::cons(Value::Int(2), Value::Int(3))
            ))
        );

        let e = "(   1 2 . 0   )".parse();
        assert_eq!(
            e,
            Ok(Value::cons(
                Value::Int(1),
                Value::cons(Value::Int(2), Value::Int(0))
            ))
        );
    }
}
