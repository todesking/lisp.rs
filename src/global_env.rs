use crate::value::Value;
use std::rc::Rc;

#[derive(Debug)]
pub struct GlobalEnv {
    values: std::collections::HashMap<String, Rc<Value>>,
}

impl GlobalEnv {
    pub fn new() -> GlobalEnv {
        GlobalEnv {
            values: std::collections::HashMap::new(),
        }
    }
    pub fn predef() -> GlobalEnv {
        let mut global = Self::new();
        global.set_value("true", Value::Bool(true));
        global.set_value("false", Value::Bool(false));
        global.set_value("+", Value::fun_reduce("+", |l: i32, r: i32| l + r));
        global.set_value("-", Value::fun_fold("-", 0, |l: i32, r: i32| l - r));
        global.set_value("*", Value::fun_reduce("*", |l: i32, r: i32| l * r));
        global.set_value("/", Value::fun2("/", |l: i32, r: i32| l / r));
        global.set_value("%", Value::fun2("%", |l: i32, r: i32| l % r));
        global
    }
    pub fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Rc<Value>> {
        self.values.get(key.as_ref()).cloned()
    }
    pub fn set<T: Into<String>>(&mut self, key: T, value: Rc<Value>) {
        self.values.insert(key.into(), value);
    }
    pub fn set_value<T: Into<String>>(&mut self, key: T, value: Value) {
        self.set(key, Rc::new(value));
    }
}
