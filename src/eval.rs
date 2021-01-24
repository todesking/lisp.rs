use std::rc::Rc;

use crate::global_env::GlobalEnv;
use crate::local_env::LocalEnv;
use crate::value::RefValue;
use crate::value::Value;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    VariableNotFound(String),
    ImproperArgs,
    ArgumentSize,
    SymbolRequired,
    InvalidArg,
    CantApply(Value),
}

pub type Result = std::result::Result<Value, EvalError>;

pub fn eval(e: &Value, global: &mut GlobalEnv) -> Result {
    eval_local_loop(e, global, None)
}

enum Cont {
    Ret(Value),
    Cont(Value, Vec<Value>),
}

impl Cont {
    fn ok_ret(v: Value) -> std::result::Result<Cont, EvalError> {
        Ok(Cont::Ret(v))
    }
    fn ok_cont(f: Value, args: Vec<Value>) -> std::result::Result<Cont, EvalError> {
        Ok(Cont::Cont(f, args))
    }
}

fn eval_local_loop(e: &Value, global: &mut GlobalEnv, local: Option<&Rc<LocalEnv>>) -> Result {
    let mut res = eval_local(e, global, local)?;
    loop {
        match res {
            Cont::Ret(v) => return Ok(v),
            Cont::Cont(f, args) => res = eval_apply(&f, args.as_ref(), global)?,
        }
    }
}

fn eval_local(
    e: &Value,
    global: &mut GlobalEnv,
    local: Option<&Rc<LocalEnv>>,
) -> std::result::Result<Cont, EvalError> {
    match e {
        Value::Int(n) => Cont::ok_ret(Value::int(*n)),
        Value::Bool(v) => Cont::ok_ret(Value::bool(*v)),
        Value::Nil => Cont::ok_ret(Value::nil()),
        Value::Sym(key) => local
            .map_or_else(
                || global.lookup(key),
                |l| match l.lookup(key) {
                    None => global.lookup(key),
                    found @ Some(_) => found,
                },
            )
            .map(Cont::Ret)
            .ok_or_else(|| EvalError::VariableNotFound(key.to_string())),
        Value::Cons(car, cdr) => match car.as_ref() {
            Value::Sym(name) if name == "quote" => match cdr.as_ref().to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [x] => Cont::ok_ret(x.as_ref().clone()),
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "define" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [name, value] => match name.as_ref() {
                        Value::Sym(name) => {
                            let value = eval_local_loop(value, global, local)?;
                            global.set(name, value);
                            Cont::ok_ret(Value::nil())
                        }
                        _ => Err(EvalError::SymbolRequired),
                    },
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "if" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [cond, th, el] => {
                        let cond = eval_local_loop(cond, global, local)?;
                        match cond {
                            Value::Bool(b) => {
                                let value = if b { th } else { el };
                                eval_local(value, global, local)
                            }
                            _ => Err(EvalError::InvalidArg),
                        }
                    }
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "lambda" => match cdr.as_ref() {
                Value::Cons(params, body) => {
                    let (param_names, rest_name) = params.collect_improper(|v| match v {
                        Value::Sym(name) => Ok(name),
                        _ => Err(EvalError::SymbolRequired),
                    })?;
                    match body.to_vec() {
                        None => Err(EvalError::ImproperArgs),
                        Some(body) => match body.as_slice() {
                            [] => Err(EvalError::ArgumentSize),
                            body => eval_lambda(&param_names, rest_name, body, local),
                        },
                    }
                }
                Value::Nil => Err(EvalError::ArgumentSize),
                _ => Err(EvalError::ImproperArgs),
            },
            f => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => {
                    let f = eval_local_loop(f, global, local)?;
                    let mut arg_values = vec![];
                    for arg in args.iter() {
                        let a = eval_local_loop(arg, global, local)?;
                        arg_values.push(a);
                    }
                    Cont::ok_cont(f, arg_values)
                }
            },
        },
        Value::Ref(r) => match r.as_ref() {
            RefValue::Lambda { .. } => unimplemented!(),
            RefValue::Fun { .. } => unimplemented!(),
        },
    }
}

fn eval_lambda(
    param_names: &[&String],
    rest_name: Option<&String>,
    body: &[Rc<Value>],
    local: Option<&Rc<LocalEnv>>,
) -> std::result::Result<Cont, EvalError> {
    let param_names: Vec<String> = param_names.iter().map(|x| (*x).clone()).collect();
    Cont::ok_ret(Value::lambda(
        param_names,
        rest_name.cloned(),
        body.iter().map(|v| v.as_ref().clone()).collect(),
        local.cloned(),
    ))
}

fn bind_args(
    param_names: &[String],
    rest_name: Option<String>,
    args: &[Value],
    parent: Option<Rc<LocalEnv>>,
) -> std::result::Result<LocalEnv, EvalError> {
    let invalid_argument_size = (rest_name.is_none() && param_names.len() != args.len())
        || (rest_name.is_some() && param_names.len() > args.len());
    if invalid_argument_size {
        Err(EvalError::ArgumentSize)
    } else {
        let mut values = std::collections::HashMap::new();
        for (k, v) in param_names.iter().zip(args) {
            values.insert(k.clone(), v.clone());
        }
        if let Some(rest_name) = rest_name {
            values.insert(rest_name, Value::from(&args[param_names.len()..]));
        }

        Ok(LocalEnv::new(values, parent))
    }
}

fn eval_apply(
    f: &Value,
    args: &[Value],
    global: &mut GlobalEnv,
) -> std::result::Result<Cont, EvalError> {
    match f {
        Value::Ref(r) => match r.as_ref() {
            RefValue::Lambda {
                param_names,
                rest_name,
                body,
                env,
            } => {
                let local = bind_args(param_names, rest_name.clone(), args, env.clone())?;
                let local = Rc::new(local);
                let mut e = Cont::Ret(Value::nil());
                if let Some((last, heads)) = body.split_last() {
                    for b in heads {
                        eval_local_loop(b, global, Some(&local))?;
                    }
                    e = eval_local(last, global, Some(&local))?;
                }
                Ok(e)
            }
            RefValue::Fun { fun, .. } => fun.0(args).map(Cont::Ret),
        },
        _ => Err(EvalError::CantApply(f.clone())),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn eval_str(s: &str, env: &mut GlobalEnv) -> Result {
        let expr = s.parse::<Value>().expect("should valid sexpr");
        eval(&expr, env)
    }

    trait Assertion {
        fn should_error(&self, err: EvalError);
        fn should_ok(&self, value: Value);
    }
    impl Assertion for Result {
        fn should_error(&self, err: EvalError) {
            assert_eq!(self, &Err(err));
        }
        fn should_ok(&self, value: Value) {
            assert_eq!(self, &Ok(value));
        }
    }

    #[test]
    fn test_list_macro() {
        assert_eq!(list!(), Value::Nil);
        assert_eq!(list!(1), Value::cons(Value::Int(1), Value::Nil));
        assert_eq!(
            list!(Value::Int(1), 2),
            Value::cons(Value::Int(1), Value::cons(Value::Int(2), Value::Nil))
        );
    }

    #[test]
    fn test_num() {
        let mut env = GlobalEnv::new();
        eval_str("1", &mut env).should_ok(1.into());
    }

    #[test]
    fn test_sym() {
        let mut env = GlobalEnv::new();
        env.set("x".to_string(), 123.into());

        eval_str("x", &mut env).should_ok(123.into());
    }

    #[test]
    fn test_nil() {
        let mut env = GlobalEnv::new();
        eval_str("()", &mut env).should_ok(Value::Nil);
    }

    #[test]
    fn test_quote() {
        let mut env = GlobalEnv::new();

        eval_str("'1", &mut env).should_ok(1.into());
        eval_str("'(1 2)", &mut env).should_ok((&vec![1, 2]).into());
        eval_str("(quote (1 2))", &mut env).should_ok((&vec![1, 2]).into());
        eval_str("(quote 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote . 1)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote 1 2)", &mut env).should_error(EvalError::ArgumentSize);
    }

    #[test]
    fn test_define() {
        let mut env = GlobalEnv::new();

        eval_str("x", &mut env).should_error(EvalError::VariableNotFound("x".into()));
        eval_str("(define x 1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1.into());

        eval_str("(define x '1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1.into());

        eval_str("(define x 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(define 1 2)", &mut env).should_error(EvalError::SymbolRequired);
        eval_str("(define x aaa)", &mut env)
            .should_error(EvalError::VariableNotFound("aaa".into()));
    }

    #[test]
    fn test_lambda_error() {
        let mut env = GlobalEnv::new();

        eval_str("(lambda)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(lambda () 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(lambda (x))", &mut env).should_error(EvalError::ArgumentSize);

        eval_str("(lambda 1 1)", &mut env).should_error(EvalError::SymbolRequired);
    }
    #[test]
    fn test_lambda_simple() {
        let mut env = GlobalEnv::new();

        eval_str("((lambda () 1))", &mut env).should_ok(1.into());
        eval_str("((lambda (x) x) 1)", &mut env).should_ok(1.into());
        eval_str("((lambda (x y) x) 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("((lambda (x y) y) 1 2)", &mut env).should_ok(2.into());
    }

    #[test]
    fn test_lambda_closure() {
        let mut env = GlobalEnv::new();

        eval_str("(((lambda (x) (lambda (y) y)) 1) 2)", &mut env).should_ok(2.into());
        eval_str("(((lambda (x) (lambda (y) x)) 1) 2)", &mut env).should_ok(1.into());
    }

    #[test]
    fn test_lambda_varargs() {
        let mut env = GlobalEnv::new();

        eval_str("(define my-list (lambda x x))", &mut env).should_ok(Value::Nil);
        eval_str("(my-list 1 2 3)", &mut env).should_ok(list!(1, 2, 3));
        eval_str("(my-list)", &mut env).should_ok(list!());

        eval_str("(define my-head (lambda (x . xs) x))", &mut env).should_ok(Value::Nil);
        eval_str("(define my-tail (lambda (x . xs) xs))", &mut env).should_ok(Value::Nil);
        eval_str("(my-head 1)", &mut env).should_ok(1.into());
        eval_str("(my-tail 1)", &mut env).should_ok(list!());
        eval_str("(my-head 1 2)", &mut env).should_ok(1.into());
        eval_str("(my-tail 1 2)", &mut env).should_ok(list!(2));
        eval_str("(my-head)", &mut env).should_error(EvalError::ArgumentSize);
    }

    #[test]
    fn test_lambda_lookup_global() {
        let mut env = GlobalEnv::new();
        env.set("x", 1.into());

        eval_str("((lambda () x))", &mut env).should_ok(1.into());
    }

    #[test]
    fn test_if() {
        let mut env = GlobalEnv::new();
        env.set("t", Value::Bool(true));
        env.set("f", Value::Bool(false));

        eval_str("(if t 1 2)", &mut env).should_ok(1.into());
        eval_str("(if f 1 2)", &mut env).should_ok(2.into());

        eval_str("(if t (define x 1) (define x 2))", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1.into());

        eval_str("(if f (define x 1) (define x 2))", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(2.into());
    }

    #[test]
    fn test_fun() {
        let mut env = GlobalEnv::new();

        env.set("f0", Value::fun0("f0", || 123));
        eval_str("(f0)", &mut env).should_ok(123.into());
        eval_str("(f0 1)", &mut env).should_error(EvalError::ArgumentSize);

        env.set("f1", Value::fun1("f1", |n: i32| n));
        eval_str("(f1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 1 2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f1 1)", &mut env).should_ok(1.into());

        env.set("f2", Value::fun2("f2", |n: i32, m: i32| n + m));
        eval_str("(f2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f2 1 2)", &mut env).should_ok(3.into());

        env.set("sum", Value::fun_fold("sum", 0, |a, x| a + x));
        eval_str("(sum)", &mut env).should_ok(0.into());
        eval_str("(sum 1)", &mut env).should_ok(1.into());
        eval_str("(sum 1 2)", &mut env).should_ok(3.into());
        eval_str("(sum 'x)", &mut env).should_error(EvalError::InvalidArg);

        env.set("sum1", Value::fun_reduce("sum1", |a: i32, x: i32| a + x));
        eval_str("(sum1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(sum1 'x)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(sum1 1)", &mut env).should_ok(1.into());
        eval_str("(sum1 1 2)", &mut env).should_ok(3.into());
    }

    #[test]
    fn test_predef_constants() {
        let mut env = GlobalEnv::predef();

        eval_str("true", &mut env).should_ok(Value::Bool(true));
        eval_str("false", &mut env).should_ok(Value::Bool(false));
    }

    #[test]
    fn test_predef_arithmetic() {
        let mut env = GlobalEnv::predef();

        eval_str("(+)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(+ 1)", &mut env).should_ok(1.into());
        eval_str("(+ 1 2)", &mut env).should_ok(3.into());

        // TODO: (-) should accept >= 1 argument
        eval_str("(-)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(- 1)", &mut env).should_ok((-1).into());
        eval_str("(- 3 8)", &mut env).should_ok((-5).into());

        eval_str("(*)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(* 1)", &mut env).should_ok(1.into());
        eval_str("(* 1 2)", &mut env).should_ok(2.into());

        eval_str("(/)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(/ 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(/ 4 2)", &mut env).should_ok(2.into());

        eval_str("(%)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(% 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(% 4 2)", &mut env).should_ok(0.into());
        // TODO: Floating point arithmetic
    }

    #[test]
    fn test_predef_eq() {
        let mut env = GlobalEnv::predef();

        eval_str("(eq? 1 1)", &mut env).should_ok(true.into());
        eval_str("(eq? 1 2)", &mut env).should_ok(false.into());

        eval_str("(eq? '(1 2 (3 4) . 5) '(1 2 (3 4) . 5))", &mut env).should_ok(true.into());

        eval_str("(eq? eq? eq?)", &mut env).should_ok(true.into());
        eval_str("(eq? eq? +)", &mut env).should_ok(false.into());
    }

    #[test]
    fn test_complex_fib() {
        let mut env = GlobalEnv::predef();

        eval_str(
            "
            (define fib (lambda (n)
                (if (eq? n 0) 0
                    (if (eq? n 1) 1
                        (+ (fib (- n 1)) (fib (- n 2)))))))",
            &mut env,
        )
        .should_ok(Value::Nil);
        eval_str("(fib 0)", &mut env).should_ok(0.into());
        eval_str("(fib 1)", &mut env).should_ok(1.into());
        eval_str("(fib 2)", &mut env).should_ok(1.into());
        eval_str("(fib 3)", &mut env).should_ok(2.into());
        eval_str("(fib 4)", &mut env).should_ok(3.into());
        eval_str("(fib 5)", &mut env).should_ok(5.into());
    }

    #[test]
    fn test_tco() {
        let env = &mut GlobalEnv::predef();

        eval_str(
            "
        (define loop (lambda (n)
            (if (eq? n 0)
                42
                (loop (- n 1)))))",
            env,
        )
        .should_ok(Value::nil());
        eval_str("(loop 100000)", env).should_ok(Value::int(42));
    }
}
