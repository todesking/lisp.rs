#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbsName(Vec<SimpleName>);
impl AbsName {
    pub fn new(parts: impl Into<Vec<SimpleName>>) -> AbsName {
        AbsName(parts.into())
    }
    pub fn global() -> AbsName {
        AbsName(vec![SimpleName::from("global").unwrap()])
    }
    pub fn root() -> AbsName {
        AbsName(vec![])
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
        let name = SimpleName::from(name).unwrap_or_else(|| {
            panic!("Not a simple name: {}", name);
        });
        self.member_name(name)
    }

    pub fn into_child_name(mut self, name: SimpleName) -> AbsName {
        self.0.push(name);
        self
    }

    pub fn into_child_name_or_die(self, name: &str) -> AbsName {
        // TODO: SimpleName::parse_or_die
        let name = SimpleName::from(name).unwrap_or_else(|| {
            panic!("Not a simple name: {}", name);
        });
        self.into_child_name(name)
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
    pub fn split(mut self) -> Option<(AbsName, SimpleName)> {
        self.0.pop().map(|n| (self, n))
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
    pub fn from<S: Into<String> + AsRef<str>>(s: S) -> Option<SimpleName> {
        if s.as_ref().chars().any(|c| c == ':') {
            None
        } else {
            Some(SimpleName(s.into()))
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
