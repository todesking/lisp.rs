fn main() -> Result<(), ParseError> {
    let s: Expr = "1".parse()?;
    println!("{:?}", s);
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
enum ParseError {
    Unexpected,
    Redundant,
}

#[derive(Debug, PartialEq, Eq)]
enum Expr {
    Int(i32),
    Cons(Box<Expr>, Box<Expr>),
}

impl Expr {
    fn int(n: i32) -> Expr {
        Expr::Int(n)
    }
    fn cons(e1: Expr, e2: Expr) -> Expr {
        Expr::Cons(Box::new(e1), Box::new(e2))
    }
}

impl std::str::FromStr for Expr {
    type Err = ParseError;
    fn from_str<'a>(s: &'a str) -> Result<Self, Self::Err> {
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

type ParseResult<'a> = Result<(Expr, &'a str), ParseError>;

fn many(s: &str, mut f: impl FnMut(char) -> bool) -> (&str, &str) {
    s.char_indices()
        .take_while(|(_, c)| f(*c))
        .last()
        .map(|(i, _)| s.split_at(i + 1))
        .unwrap_or(("", s))
}

fn skip_ws(s: &str) -> &str {
    many(s, |c| c == ' ').1
}

fn consume<'a>(s: &'a str, pat: &str) -> Option<&'a str> {
    if s.starts_with(pat) {
        Some(&s[pat.len()..])
    } else {
        None
    }
}

fn parse_expr(s: &str) -> Result<(Expr, &str), ParseError> {
    parse_num(s).or_else(|_| parse_cons(s))
}

fn parse_num(s: &str) -> ParseResult {
    let (s1, s2) = many(s, |c| '0' <= c && c <= '9');
    if s1.is_empty() {
        Err(ParseError::Unexpected)
    } else {
        Ok((Expr::int(s1.parse().expect("should not reach here")), s2))
    }
}

fn parse_cons(s: &str) -> ParseResult {
    let s = consume(s, "(").ok_or(ParseError::Unexpected)?;
    let s = skip_ws(s);

    let (e1, s) = parse_expr(s)?;
    let s = skip_ws(s);

    let s = consume(s, ".").ok_or(ParseError::Unexpected)?;
    let s = skip_ws(s);

    let (e2, s) = parse_expr(s)?;
    let s = skip_ws(s);

    let s = consume(s, ")").ok_or(ParseError::Unexpected)?;

    Ok((Expr::cons(e1, e2), s))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_num() {
        let e = "1".parse();
        assert_eq!(e, Ok(Expr::int(1)));

        let e = "123".parse();
        assert_eq!(e, Ok(Expr::int(123)));

        let e = "   123".parse();
        assert_eq!(e, Ok(Expr::int(123)));

        let e = "123    ".parse();
        assert_eq!(e, Ok(Expr::int(123)));

        let e: Result<Expr, ParseError> = "123a".parse();
        assert_eq!(e, Err(ParseError::Redundant));

        let e: Result<Expr, ParseError> = "aaa".parse();
        assert_eq!(e, Err(ParseError::Unexpected));
    }

    #[test]
    fn test_cons() {
        let e = "(1.2)".parse();
        assert_eq!(e, Ok(Expr::cons(Expr::int(1), Expr::int(2))));

        let e = "(  3 . 4  )".parse();
        assert_eq!(e, Ok(Expr::cons(Expr::int(3), Expr::int(4))));
    }
}
