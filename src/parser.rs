use crate::value::Value;

#[derive(Debug, PartialEq, Eq)]
pub enum ParseError {
    Unexpected,
    Redundant,
}

impl std::str::FromStr for Value {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = skip_ws(s);
        let (e, s) = parse_expr(s)?;
        let s = skip_ws(s);
        if !s.is_empty() {
            Err(ParseError::Redundant)
        } else {
            Ok(e)
        }
    }
}

type ParseResult<'a> = Result<(Value, &'a str), ParseError>;

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
    s.strip_prefix(pat).ok_or(ParseError::Unexpected)
}

fn parse_expr(s: &str) -> ParseResult {
    parse_quote(s)
        .or_else(|_| parse_num(s))
        .or_else(|_| parse_list(s))
        .or_else(|_| parse_symbol(s))
}

fn parse_quote(s: &str) -> ParseResult {
    let s = consume(s, "'")?;
    let (e, s) = parse_expr(s)?;
    let e = Value::cons(Value::sym("quote"), Value::cons(e, Value::Nil));
    Ok((e, s))
}

fn parse_num(s: &str) -> ParseResult {
    let (s1, s2) = many(s, |c| '0' <= c && c <= '9');
    if s1.is_empty() {
        Err(ParseError::Unexpected)
    } else {
        Ok((Value::Int(s1.parse().expect("should not reach here")), s2))
    }
}

fn parse_symbol(s: &str) -> ParseResult {
    let (s1, s2) = many(
        s,
        |c| matches!( c, 'a'..='z' | 'A'..='Z' | '0'..='9' | '+' | '-' | '*' | '/' | '%' | '?' | '!' | '\''),
    );
    match s1 {
        "" => Err(ParseError::Unexpected),
        "'" => Err(ParseError::Unexpected),
        name => Ok((Value::sym(name), s2)),
    }
}

fn parse_list(s: &str) -> ParseResult {
    let s = consume(s, "(")?;
    let s = skip_ws(s);

    let mut items = Vec::new();
    let mut s = s;
    while let Ok((e, s1)) = parse_expr(s) {
        items.push(e);
        s = skip_ws(s1);
    }

    let (tail, s) = if let Ok(s) = consume(s, ".") {
        let s = skip_ws(s);
        let (e, s) = parse_expr(s)?;
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
        assert_eq!(e, Err(ParseError::Redundant));
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
        assert_eq!(e, Err(ParseError::Unexpected));

        let e = "' 1".parse::<Value>();
        assert_eq!(e, Err(ParseError::Unexpected));

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
