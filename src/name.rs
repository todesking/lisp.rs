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

    // TODO: Make name: SimpleName
    pub fn child_name(&self, name: &SimpleName) -> AbsName {
        let mut abs_name = self.clone();
        abs_name.0.push(name.clone());
        abs_name
    }

    pub fn child_name_or_die(&self, name: &str) -> AbsName {
        let name = SimpleName::from(name).unwrap();
        self.child_name(&name)
    }

    pub fn relative_name(&self, names: impl IntoIterator<Item = SimpleName>) -> AbsName {
        let mut v = self.0.clone();
        for name in names {
            v.push(name);
        }
        AbsName(v)
    }

    // TODO: remove this
    pub fn split(&self) -> (AbsName, SimpleName) {
        let last = self.0.last().unwrap().clone();
        let mut heads = self.0.clone();
        heads.pop();
        (AbsName(heads), last)
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
