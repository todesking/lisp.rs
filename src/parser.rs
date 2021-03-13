use crate::Value;

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
    let s = many(s, |c| c == ' ' || c == '\n').1;
    if s.starts_with(';') {
        let s = s.find('\n').map(|i| &s[i + 1..]).unwrap_or(&"");
        skip_ws(s)
    } else {
        s
    }
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
        .or_else(|_| parse_quasiquote(p, s))
        .or_else(|_| parse_unquote_splicing(p, s))
        .or_else(|_| parse_unquote(p, s))
        .or_else(|_| parse_str(s))
        .or_else(|_| parse_num(s))
        .or_else(|_| parse_list(p, s))
        .or_else(|_| parse_symbol(p, s))
}

fn parse_quote<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let s = consume(s, "'")?;
    let (e, s) = parse_expr(p, s)?;
    let e = list![p.new_sym("quote"), e];
    Ok((e, s))
}

fn parse_quasiquote<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let s = consume(s, "`")?;
    let (e, s) = parse_expr(p, s)?;
    let e = list![p.new_sym("quasiquote"), e];
    Ok((e, s))
}

fn parse_unquote_splicing<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let s = consume(s, ",@")?;
    let (e, s) = parse_expr(p, s)?;
    let e = list![p.new_sym("unquote-splicing"), e];
    Ok((e, s))
}

fn parse_unquote<'p, 's>(p: &'p mut Parser, s: &'s str) -> ParseResult<'s> {
    let s = consume(s, ",")?;
    let (e, s) = parse_expr(p, s)?;
    let e = list![p.new_sym("unquote"), e];
    Ok((e, s))
}

fn parse_str(s: &str) -> ParseResult {
    let s = consume(s, "\"")?;
    let (content, s) = parse_str_body(s)?;
    let s = consume(s, "\"")?;
    Ok((Value::str(&content), s))
}

fn parse_str_body(s: &str) -> Result<(String, &str), ParseError> {
    let mut content = String::new();
    let mut iter = s.char_indices();
    loop {
        if let Some((i, ch)) = iter.next() {
            match ch {
                '\\' => {
                    if let Some((_, ch)) = iter.next() {
                        let ch = match ch {
                            'n' => '\n',
                            '\\' => '\\',
                            '"' => '"',
                            _ => return Err(ParseError::Unexpected(format!("\\{}", ch))),
                        };
                        content.push(ch);
                    } else {
                        return Err(ParseError::Unexpected("".to_owned()));
                    }
                }
                '"' => {
                    return Ok((content, &s[i..]));
                }
                _ => {
                    content.push(ch);
                }
            }
        } else {
            return Err(ParseError::Unexpected("".to_owned()));
        }
    }
}

fn parse_num(s: &str) -> ParseResult {
    let (minus, s) = try_consume(s, "-");
    let (s1, s2) = many(s, |c| ('0'..='9').contains(&c));
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
        |c| matches!( c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '+' | '-' | '*' | '/' | '%' | '?' | '!' | '\'' | '<' | '>' | '=' | '#' | '_' | ':'),
    );
    match s1 {
        "" => Err(ParseError::Unexpected(s2.to_owned())),
        "'" => Err(ParseError::Unexpected(s2.to_owned())),
        "#t" => Ok((Value::Bool(true), s2)),
        "#f" => Ok((Value::Bool(false), s2)),
        name if s1.starts_with('#') => Err(ParseError::Unexpected(name.to_owned())),
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

    fn parse(s: &str) -> Result<Value, ParseError> {
        s.parse()
    }
    trait Assertions {
        fn should_ok<V: Into<Value>>(&self, v: V);
        fn should_error(&self, e: ParseError);
    }
    impl Assertions for Result<Value, ParseError> {
        fn should_ok<V: Into<Value>>(&self, v: V) {
            assert_eq!(self, &Ok(v.into()));
        }
        fn should_error(&self, e: ParseError) {
            assert_eq!(self, &Err(e));
        }
    }

    #[test]
    fn test_string() {
        parse(r#""foo""#).should_ok(Value::str("foo"));
        parse(r#""foo\nbar""#).should_ok(Value::str("foo\nbar"));
        parse(r#""\\""#).should_ok(Value::str("\\"));
        parse(r#""\"""#).should_ok(Value::str("\""));
        parse(r#"""#).should_error(ParseError::Unexpected("\"".to_owned()));
        parse(r#""foo"#).should_error(ParseError::Unexpected("\"foo".to_owned()));
    }

    #[test]
    fn test_num() {
        parse("1").should_ok(1);
        parse("123").should_ok(123);
        parse("   123").should_ok(123);
        parse("123   ").should_ok(123);
        parse("123a").should_error(ParseError::Redundant("a".to_owned()));
        parse("-123").should_ok(-123);
    }

    #[test]
    fn test_symbol() {
        parse("a").should_ok(Value::sym("a"));
        parse("LONG-symbol'name?!?!").should_ok(Value::sym("LONG-symbol'name?!?!"));
        parse("f0").should_ok(Value::sym("f0"));
        parse("+-*/%<>=#_:").should_ok(Value::sym("+-*/%<>=#_:"));
        parse("#unknown-symbol").should_error(ParseError::Unexpected("#unknown-symbol".to_owned()));
    }

    #[test]
    fn test_bool() {
        parse("#t").should_ok(Value::Bool(true));
        parse("#f").should_ok(Value::Bool(false));
    }

    #[test]
    fn test_quote() {
        parse("'").should_error(ParseError::Unexpected("".to_owned()));
        parse("' 1").should_error(ParseError::Unexpected(" 1".to_owned()));
        parse("'1").should_ok(list![Value::sym("quote"), 1]);
        parse("'()").should_ok(list![Value::sym("quote"), Value::nil()]);
    }

    #[test]
    fn test_cons() {
        parse("(1.2)").should_ok(list![1; 2]);
        parse("(  3 . 4  )").should_ok(list![3; 4]);
    }

    #[test]
    fn test_list() {
        parse("()").should_ok(list![]);
        parse("(1 2 3)").should_ok(list![1, 2, 3]);
        parse("(1 2 . 3)").should_ok(list![1,2; 3]);
        parse("(   1 2 . 0   )").should_ok(list![1, 2; 0]);
    }

    #[test]
    fn test_quasiquote() {
        parse("`").should_error(ParseError::Unexpected("`".to_owned()));
        parse("` 1").should_error(ParseError::Unexpected("` 1".to_owned()));
        parse("`1").should_ok(list![Value::sym("quasiquote"), 1]);

        parse(",").should_error(ParseError::Unexpected(",".to_owned()));
        parse(", 1").should_error(ParseError::Unexpected(", 1".to_owned()));
        parse(",1").should_ok(list![Value::sym("unquote"), 1]);

        parse(",@").should_error(ParseError::Unexpected(",@".to_owned()));
        parse(",@ 1").should_error(ParseError::Unexpected(",@ 1".to_owned()));
        parse(",@1").should_ok(list![Value::sym("unquote-splicing"), 1]);

        parse("`(1 2 ,x ,@xs)").should_ok(list![
            Value::sym("quasiquote"),
            list![
                1,
                2,
                list![Value::sym("unquote"), Value::sym("x")],
                list![Value::sym("unquote-splicing"), Value::sym("xs")]
            ]
        ]);
    }
    #[test]
    fn test_comment() {
        parse("1 ; aaaa").should_ok(1);
        parse(
            "(; aaa
        1; bbb
        ;ccc
        2); ddd",
        )
        .should_ok(list![1, 2]);
    }
}
