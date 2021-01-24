use crate::value::Value;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub struct LocalEnv {
    values: std::collections::HashMap<Rc<str>, Value>,
    parent: Option<Rc<RefCell<LocalEnv>>>,
}

impl LocalEnv {
    pub fn new(
        values: std::collections::HashMap<Rc<str>, Value>,
        parent: Option<Rc<RefCell<LocalEnv>>>,
    ) -> LocalEnv {
        LocalEnv { values, parent }
    }
    pub fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Value> {
        self.values
            .get(key.as_ref())
            .cloned()
            .or_else(|| match &self.parent {
                None => None,
                Some(l) => l.borrow().lookup(key),
            })
    }
    pub fn set_if_defined<T: AsRef<str>>(&mut self, name: T, value: Value) -> bool {
        if let Some(target) = self.values.get_mut(name.as_ref()) {
            *target = value;
            true
        } else {
            self.parent
                .as_ref()
                .map_or_else(|| false, |l| l.borrow_mut().set_if_defined(name, value))
        }
    }
}
