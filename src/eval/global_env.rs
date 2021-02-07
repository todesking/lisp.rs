use crate::eval::EvalError;
use crate::value::Value;

#[derive(Debug, Default)]
pub struct GlobalEnv {
    ids: std::collections::HashMap<String, usize>,
    values: Vec<Value>,
}

impl GlobalEnv {
    pub fn new() -> GlobalEnv {
        GlobalEnv {
            ids: std::collections::HashMap::new(),
            values: Vec::new(),
        }
    }
    pub fn lookup_global_id(&self, name: &str) -> Option<usize> {
        self.ids.get(name).copied()
    }

    pub fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<&Value> {
        self.lookup_global_id(key.as_ref()).map(|i| &self.values[i])
    }

    pub fn next_id(&self) -> usize {
        self.values.len()
    }

    pub fn get(&self, id: usize) -> &Value {
        &self.values[id]
    }
    pub fn set_by_id(&mut self, id: usize, value: Value) {
        self.values[id] = value;
    }
    pub fn set<T: Into<String>>(&mut self, key: T, value: Value) {
        let key = key.into();
        if let Some(id) = self.lookup_global_id(&key) {
            self.values[id] = value;
        } else {
            self.values.push(value);
            self.ids.insert(key, self.values.len() - 1);
        }
    }
    pub fn set_fun<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&[Value]) -> Result<Value, EvalError> + 'static,
    {
        let value = Value::fun(name, f);
        self.set(name.to_string(), value);
    }
    pub fn set_fun1<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&Value) -> Result<Value, EvalError> + 'static,
    {
        self.set_fun(name, move |args| {
            if args.len() != 1 {
                Err(EvalError::IllegalArgument(Value::list(args.iter())))
            } else {
                f(&args[0])
            }
        })
    }
    pub fn set_fun2<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&Value, &Value) -> Result<Value, EvalError> + 'static,
    {
        self.set_fun(name, move |args| {
            if args.len() != 2 {
                Err(EvalError::IllegalArgument(Value::list(args.iter())))
            } else {
                f(&args[0], &args[1])
            }
        })
    }
    pub fn ls(&self) -> impl Iterator<Item = &str> {
        self.ids.keys().map(|s| s.as_ref())
    }
}
