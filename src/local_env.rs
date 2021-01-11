use crate::value::Value;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub struct LocalEnv {
    values: std::collections::HashMap<String, Rc<Value>>,
    parent: Option<Rc<LocalEnv>>,
}

impl LocalEnv {
    pub fn new(
        values: std::collections::HashMap<String, Rc<Value>>,
        parent: Option<Rc<LocalEnv>>,
    ) -> LocalEnv {
        LocalEnv { values, parent }
    }
    pub fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Rc<Value>> {
        self.values
            .get(key.as_ref())
            .cloned()
            .or_else(|| match &self.parent {
                None => None,
                Some(l) => l.lookup(key),
            })
    }
}
