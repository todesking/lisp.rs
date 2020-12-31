use io::Write;
use io::{stdin, stdout};
use std::io; // for flush()

fn main() -> io::Result<()> {
    loop {
        print!("LISP.rs> ");
        stdout().flush()?;

        let mut buf = String::new();
        let nread = stdin().read_line(&mut buf)?;
        if nread == 0 {
            // eof
            break;
        }

        if buf == "" {
            continue;
        }
        if buf == ":q" {
            break;
        }

        let e = buf.parse::<Expr>();
        println!("=> {:?}", e);
    }
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
    Nil,
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

type ParseResult<'a> = Result<(Expr, &'a str), ParseError>;

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

fn parse_expr(s: &str) -> Result<(Expr, &str), ParseError> {
    parse_num(s).or_else(|_| parse_list(s))
}

fn parse_num(s: &str) -> ParseResult {
    let (s1, s2) = many(s, |c| '0' <= c && c <= '9');
    if s1.is_empty() {
        Err(ParseError::Unexpected)
    } else {
        Ok((Expr::int(s1.parse().expect("should not reach here")), s2))
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
        (Expr::Nil, s)
    };

    let s = consume(s, ")")?;
    let e = items.into_iter().rev().fold(tail, |a, x| Expr::cons(x, a));

    Ok((e, s))
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

    #[test]
    fn test_list() {
        let e = "()".parse();
        assert_eq!(e, Ok(Expr::Nil));

        let e = "(1 2 3)".parse();
        assert_eq!(
            e,
            Ok(Expr::cons(
                Expr::int(1),
                Expr::cons(Expr::int(2), Expr::cons(Expr::int(3), Expr::Nil))
            ))
        );

        let e = "(1 2 . 3)".parse();
        assert_eq!(
            e,
            Ok(Expr::cons(
                Expr::int(1),
                Expr::cons(Expr::int(2), Expr::int(3))
            ))
        );

        let e = "(   1 2 . 0   )".parse();
        assert_eq!(
            e,
            Ok(Expr::cons(
                Expr::int(1),
                Expr::cons(Expr::int(2), Expr::int(0))
            ))
        );
    }
}
