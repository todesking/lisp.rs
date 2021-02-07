use crate::value::Value;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Default)]
pub struct LocalEnv {
    // value(depth, index) = values[depth - 1][index]
    values: Vec<Rc<RefCell<Vec<Value>>>>,
}

impl LocalEnv {
    pub fn new() -> LocalEnv {
        Default::default()
    }
    pub fn extend(&self, args: Rc<RefCell<Vec<Value>>>) -> LocalEnv {
        let mut values = self.values.clone();
        values.push(args);
        LocalEnv { values }
    }
    pub fn get(&self, depth: usize, index: usize) -> Value {
        self.values[depth - 1].as_ref().borrow()[index].clone()
    }
    pub fn set(&self, depth: usize, index: usize, value: Value) {
        let mut v = self.values[depth - 1].as_ref().borrow_mut();
        v[index] = value;
    }
}
