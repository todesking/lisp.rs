use crate::value::Value;
use std::rc::Rc;

#[derive(Debug, Default)]
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
        global.set_fun("eq?", |args| {
            if args.len() != 2 {
                Err(crate::eval::EvalError::ArgumentSize)
            } else {
                Ok(Rc::new(Value::Bool(args[0] == args[1])))
            }
        });
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
    pub fn set_fun<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&[Rc<Value>]) -> Result<Rc<Value>, crate::eval::EvalError> + 'static,
    {
        let value = Value::Fun(crate::value::FunData {
            name: name.to_string(),
            fun: Rc::new(f),
        });
        let value = Rc::new(value);
        self.set(name.to_string(), value);
    }
}
