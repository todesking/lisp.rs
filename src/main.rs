fn main() -> Result<(), ParseError> {
    let s: Expr = "1".parse()?;
    println!("{:?}", s);
    Ok(())
}

#[derive(Debug, PartialEq, Eq)]
enum ParseError {
    Unexpected(String),
    Redundant(String),
    EOF,
}

#[derive(Debug, PartialEq, Eq)]
enum Expr {
    Int(i32),
}

impl std::str::FromStr for Expr {
    type Err = ParseError;
    fn from_str<'a>(s: &'a str) -> Result<Self, Self::Err> {
        let (e, s) = parse_expr(s)?;
        if !s.is_empty() {
            Err(ParseError::Redundant(s.to_owned()))
        } else {
            Ok(e)
        }
    }
}

type ParseResult<'a> = Result<(Expr, &'a str), ParseError>;

fn parse_expr(s: &str) -> Result<(Expr, &str), ParseError> {
    match s.chars().next() {
        Some(c) => match c {
            '0'..='9' => parse_num(s),
            _ => Err(ParseError::Unexpected(s.to_owned())),
        },
        None => Err(ParseError::EOF),
    }
}

fn many(s: &str, mut f: impl FnMut(char) -> bool) -> Option<(&str, &str)> {
    s.char_indices()
        .take_while(|(_, c)| f(*c))
        .last()
        .map(|(i, _)| s.split_at(i + 1))
}

fn parse_num(s: &str) -> ParseResult {
    many(s, |c| '0' <= c && c <= '9')
        .filter(|(s1, _)| !s1.is_empty())
        .map(|(s1, s2)| (Expr::Int(s1.parse().unwrap()), s2))
        .ok_or(ParseError::Unexpected(s.to_owned()))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_num() {
        println!("{:?}", parse_expr("1"));
        let e = "1".parse();
        assert_eq!(e, Ok(Expr::Int(1)));

        let e = "123".parse();
        assert_eq!(e, Ok(Expr::Int(123)));

        let e: Result<Expr, ParseError> = "123a".parse();
        assert_eq!(e, Err(ParseError::Redundant("a".to_owned())));

        let e: Result<Expr, ParseError> = "aaa".parse();
        assert_eq!(e, Err(ParseError::Unexpected("aaa".to_owned())));
    }
}
