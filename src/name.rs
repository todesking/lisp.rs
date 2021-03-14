#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbsName(Vec<SimpleName>);
impl AbsName {
    pub fn new(parts: impl Into<Vec<SimpleName>>) -> AbsName {
        AbsName(parts.into())
    }
    pub fn global() -> AbsName {
        AbsName(vec![SimpleName::parse_or_die("global")])
    }
    pub fn root() -> AbsName {
        AbsName(vec![])
    }
    pub fn parse(s: &str) -> Option<AbsName> {
        let (parts, is_abs) = SimpleName::split(s)?;
        if !is_abs {
            None
        } else {
            Some(Self::new(parts))
        }
    }

    pub fn member_name(&self, name: SimpleName) -> MemberName {
        self.clone().into_member_name(name)
    }

    pub fn into_member_name(self, name: SimpleName) -> MemberName {
        MemberName::new(self, name)
    }

    pub fn try_into_member_name(mut self) -> Option<MemberName> {
        self.0.pop().map(|name| MemberName::new(self, name))
    }

    pub fn member_name_or_die(&self, name: &str) -> MemberName {
        self.member_name(SimpleName::parse_or_die(name))
    }

    pub fn into_child_name(mut self, name: SimpleName) -> AbsName {
        self.0.push(name);
        self
    }

    pub fn into_child_name_or_die(self, name: &str) -> AbsName {
        self.into_child_name(SimpleName::parse_or_die(name))
    }

    pub fn into_descendant_name(mut self, names: impl IntoIterator<Item = SimpleName>) -> AbsName {
        for name in names {
            self.0.push(name);
        }
        self
    }

    pub fn relative_name(&self, names: impl IntoIterator<Item = SimpleName>) -> AbsName {
        let mut v = self.0.clone();
        for name in names {
            v.push(name);
        }
        AbsName(v)
    }
}
impl std::fmt::Display for AbsName {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        use std::fmt::Write;
        for part in &self.0 {
            fmt.write_char(':')?;
            part.fmt(fmt)?;
        }
        Ok(())
    }
}

// TODO: Use Rc<str>
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SimpleName(String);
impl SimpleName {
    pub unsafe fn new_unchecked<S: Into<String>>(s: S) -> SimpleName {
        SimpleName(s.into())
    }
    pub fn parse<S: Into<String> + AsRef<str>>(s: S) -> Option<SimpleName> {
        if s.as_ref().chars().any(|c| c == ':') {
            None
        } else {
            Some(SimpleName(s.into()))
        }
    }
    pub fn parse_or_die(s: &str) -> SimpleName {
        Self::parse(s).unwrap_or_else(|| {
            panic!("Not a simple name: {}", s);
        })
    }
    /// `SimpleName::split("")` and `SimpleName::split(":")` will return None.
    /// Note: Empty vector is never returned.
    pub fn split(s: &str) -> Option<(Vec<SimpleName>, bool)> {
        let parts = s.split(':').collect::<Vec<_>>();
        if parts.is_empty() || parts[1..].iter().any(|p| p.is_empty()) {
            None
        } else {
            let is_abs = parts[0].is_empty();
            let make_simple_name = |s: &str| unsafe { SimpleName::new_unchecked(s.to_owned()) };
            let parts = if is_abs {
                parts[1..]
                    .iter()
                    .map(|&p| make_simple_name(p))
                    .collect::<Vec<_>>()
            } else {
                parts.into_iter().map(make_simple_name).collect::<Vec<_>>()
            };
            Some((parts, is_abs))
        }
    }
}
impl AsRef<str> for SimpleName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}
impl std::fmt::Display for SimpleName {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str(&self.0)?;
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MemberName {
    pub module_name: AbsName,
    pub simple_name: SimpleName,
}
impl MemberName {
    pub fn new(module_name: AbsName, simple_name: SimpleName) -> MemberName {
        MemberName {
            module_name,
            simple_name,
        }
    }
    pub fn parse(s: &str) -> Option<MemberName> {
        AbsName::parse(s).and_then(|n| n.try_into_member_name())
    }
    pub fn parse_or_die(s: &str) -> MemberName {
        Self::parse(s).unwrap_or_else(|| panic!("Not a member name: {}", s))
    }
    pub fn to_abs_name(&self) -> AbsName {
        self.clone().into_abs_name()
    }
    pub fn into_abs_name(self) -> AbsName {
        self.module_name.into_child_name(self.simple_name)
    }
}
impl std::fmt::Display for MemberName {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        use std::fmt::Write;
        self.module_name.fmt(fmt)?;
        fmt.write_char(':')?;
        self.simple_name.fmt(fmt)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Name {
    Single(SimpleName),
    Relative(Vec<SimpleName>, SimpleName),
    Absolute(MemberName),
}
impl Name {
    pub fn parse(name: &str) -> Option<Name> {
        let (parts, is_abs) = SimpleName::split(name)?;
        if is_abs {
            AbsName::new(parts)
                .try_into_member_name()
                .map(Name::Absolute)
        } else if parts.len() == 1 {
            Some(Name::Single(parts[0].clone()))
        } else {
            assert!(parts.len() > 1);
            let mut parts = parts;
            let last = parts.pop().unwrap_or_else(|| unreachable!());
            let prefix = parts;
            Some(Name::Relative(prefix, last))
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_name() {
        assert_eq!(
            Name::parse("foo"),
            Some(Name::Single(SimpleName::parse_or_die("foo")))
        );
        assert_eq!(
            Name::parse(":foo"),
            Some(Name::Absolute(MemberName::parse(":foo").unwrap()))
        );
        assert_eq!(
            Name::parse("foo:bar"),
            Some(Name::Relative(
                vec![SimpleName::parse_or_die("foo")],
                SimpleName::parse_or_die("bar")
            ))
        );
        assert_eq!(
            Name::parse(":foo:bar:baz"),
            Some(Name::Absolute(MemberName::parse_or_die(":foo:bar:baz")))
        );
        assert_eq!(Name::parse(""), None);
        assert_eq!(Name::parse(":"), None);
        assert_eq!(Name::parse(":foo:"), None);
        assert_eq!(Name::parse(":foo::bar"), None);
    }
}
