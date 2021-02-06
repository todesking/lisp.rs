use crate::eval::EvalError;
use crate::eval_str_or_panic;
use crate::value::Extract;
use crate::value::Value;

#[derive(Debug, Default)]
pub struct GlobalEnv {
    values: std::collections::HashMap<String, Value>,
}

impl GlobalEnv {
    pub fn new() -> GlobalEnv {
        GlobalEnv {
            values: std::collections::HashMap::new(),
        }
    }
    pub fn predef() -> GlobalEnv {
        let mut global = Self::new();

        global.set("true", Value::Bool(true));
        global.set("false", Value::Bool(false));

        global.set_fun("error", |args| Err(EvalError::User(Value::list(args))));
        eval_str_or_panic(
            "
            (define assert-eq
                (lambda (expected actual)
                    (if (eq? expected actual) () (error 'assert-eq expected actual))))",
            &mut global,
        );
        eval_str_or_panic(
            "(define assert-error
                (lambda (f err)
                    (assert-eq
                        (catch-error
                            (lambda (err x) (cons err x))
                            (f))
                        err)))",
            &mut global,
        );

        global.set("+", Value::fun_reduce("+", |l: i32, r: i32| l + r));
        global.set_fun("-", |args| {
            let mut it = args.iter();
            let x0 = it
                .next()
                .ok_or_else(|| EvalError::IllegalArgument(Value::list(args)))?;
            let x0 = i32::extract(x0).ok_or(EvalError::InvalidArg)?;
            if let Some(x1) = it.next() {
                // binary or more
                let x1 = i32::extract(x1).ok_or(EvalError::InvalidArg)?;
                let mut a = x0 - x1;
                for xn in it {
                    let xn = i32::extract(xn).ok_or(EvalError::InvalidArg)?;
                    a -= xn;
                }
                Ok(Value::int(a))
            } else {
                // unary
                Ok(Value::int(-x0))
            }
        });
        global.set("*", Value::fun_reduce("*", |l: i32, r: i32| l * r));
        global.set("/", Value::fun2("/", |l: i32, r: i32| l / r));
        global.set("%", Value::fun2("%", |l: i32, r: i32| l % r));
        global.set_fun("eq?", |args| {
            if args.len() != 2 {
                Err(crate::eval::EvalError::IllegalArgument(Value::list(args)))
            } else {
                Ok(Value::bool(args[0] == args[1]))
            }
        });

        global.set(
            "cons",
            Value::fun("cons", |args| {
                let mut it = args.iter();
                let x1 = it
                    .next()
                    .ok_or_else(|| EvalError::IllegalArgument(Value::list(args)))?;
                let x2 = it
                    .next()
                    .ok_or_else(|| EvalError::IllegalArgument(Value::list(args)))?;
                if it.next() == None {
                    Ok(Value::cons(x1.clone(), x2.clone()))
                } else {
                    Err(EvalError::IllegalArgument(Value::list(args)))
                }
            }),
        );
        eval_str_or_panic("(define list (lambda x x))", &mut global);
        global.set(
            "car",
            Value::fun("car", |args| {
                if args.len() != 1 {
                    Err(EvalError::IllegalArgument(Value::list(args)))
                } else if let Some((car, _)) = args[0].to_cons() {
                    Ok(car)
                } else {
                    Err(EvalError::InvalidArg)
                }
            }),
        );
        global.set(
            "cdr",
            Value::fun("cdr", |args| {
                if args.len() != 1 {
                    Err(EvalError::IllegalArgument(Value::list(args)))
                } else if let Some((_, cdr)) = args[0].to_cons() {
                    Ok(cdr)
                } else {
                    Err(EvalError::InvalidArg)
                }
            }),
        );
        global.set_fun2("set-car!", |x, v| x.set_car(v.clone(), true));
        global.set_fun2("set-cdr!", |x, v| x.set_cdr(v.clone(), true));
        global.set_fun2("unsafe-set-car!", |x, v| x.set_car(v.clone(), false));
        global.set_fun2("unsafe-set-cdr!", |x, v| x.set_cdr(v.clone(), false));

        global
    }
    pub fn lookup<T: AsRef<str>>(&self, key: &T) -> Option<Value> {
        self.values.get(key.as_ref()).cloned()
    }
    pub fn set<T: Into<String>>(&mut self, key: T, value: Value) {
        self.values.insert(key.into(), value);
    }
    pub fn set_fun<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&[Value]) -> Result<Value, crate::eval::EvalError> + 'static,
    {
        let value = Value::fun(name, f);
        self.set(name.to_string(), value);
    }
    pub fn set_fun2<F>(&mut self, name: &str, f: F)
    where
        F: Fn(&Value, &Value) -> Result<Value, crate::eval::EvalError> + 'static,
    {
        self.set_fun(name, move |args| {
            if args.len() != 2 {
                Err(crate::eval::EvalError::IllegalArgument(Value::list(args)))
            } else {
                f(&args[0], &args[1])
            }
        })
    }
    pub fn ls(&self) -> impl Iterator<Item = &str> {
        self.values.keys().map(|s| s.as_ref())
    }
}
