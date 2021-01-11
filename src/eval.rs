use std::rc::Rc;

use crate::global_env::GlobalEnv;
use crate::local_env::LocalEnv;
use crate::value::Value;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    VariableNotFound(String),
    ImproperArgs,
    ArgumentSize,
    SymbolRequired,
    InvalidArg,
    CantApply(Rc<Value>),
}

pub type Result = std::result::Result<Rc<Value>, EvalError>;

pub fn eval(e: &Value, global: &mut GlobalEnv) -> Result {
    eval_local(e, global, None)
}

fn eval_local(e: &Value, global: &mut GlobalEnv, local: Option<&Rc<LocalEnv>>) -> Result {
    match e {
        Value::Int(n) => Ok(Rc::new(Value::Int(*n))),
        Value::Bool(b) => Ok(Rc::new(Value::Bool(*b))),
        Value::Nil => Ok(Rc::new(Value::Nil)),
        Value::Sym(key) => local
            .map_or_else(
                || global.lookup(key),
                |l| match l.lookup(key) {
                    None => global.lookup(key),
                    found @ Some(_) => found,
                },
            )
            .ok_or_else(|| EvalError::VariableNotFound(key.to_string())),
        Value::Lambda(_, _, _, _) => unimplemented!(),
        Value::Fun(_) => unimplemented!(),
        Value::Cons(car, cdr) => match car.as_ref() {
            Value::Sym(name) if name == "quote" => match cdr.as_ref().to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [x] => Ok(x.clone()),
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name == "define" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [name, value] => match name.as_ref() {
                        Value::Sym(name) => {
                            let value = eval_local(value, global, local)?;
                            global.set(name, value);
                            Ok(Rc::new(Value::Nil))
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
                        let cond = eval_local(cond, global, local)?;
                        match cond.as_ref() {
                            Value::Bool(b) => {
                                let value = if *b { th } else { el };
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
                    let f = eval_local(f, global, local)?;
                    let mut arg_values = vec![];
                    for arg in args.iter() {
                        let a = eval_local(arg, global, local)?;
                        arg_values.push(a);
                    }
                    eval_apply(&f, &arg_values, global)
                }
            },
        },
    }
}

fn eval_lambda(
    param_names: &[&String],
    rest_name: Option<&String>,
    body: &[Rc<Value>],
    local: Option<&Rc<LocalEnv>>,
) -> Result {
    let param_names: Vec<String> = param_names.iter().map(|x| (*x).clone()).collect();
    let body: Vec<Rc<Value>> = body.to_vec();
    Ok(Rc::new(Value::Lambda(
        param_names,
        rest_name.cloned(),
        body,
        local.cloned(),
    )))
}

fn bind_args(
    param_names: &[String],
    rest_name: Option<String>,
    args: &[Rc<Value>],
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
            values.insert(rest_name, Rc::new(Value::from(&args[param_names.len()..])));
        }

        Ok(LocalEnv::new(values, parent))
    }
}

fn eval_apply(f: &Rc<Value>, args: &[Rc<Value>], global: &mut GlobalEnv) -> Result {
    match f.as_ref() {
        Value::Lambda(param_names, rest_name, body, parent) => {
            let local = bind_args(param_names, rest_name.clone(), args, parent.clone())?;
            let local = Rc::new(local);
            let mut e = Rc::new(Value::Nil);
            for b in body {
                e = eval_local(b, global, Some(&local))?;
            }
            Ok(e)
        }
        Value::Fun(crate::value::FunData { fun, .. }) => fun(args),
        _ => Err(EvalError::CantApply(f.clone())),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parser::Expr;

    fn eval_str(s: &str, env: &mut GlobalEnv) -> Result {
        let expr = s.parse::<Expr>().expect("should valid sexpr");
        eval(&(&expr).into(), env)
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
            assert_eq!(self, &Ok(Rc::new(value)));
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
        env.set("x".to_string(), Rc::new(123.into()));

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
        env.set_value("x", 1.into());

        eval_str("((lambda () x))", &mut env).should_ok(1.into());
    }

    #[test]
    fn test_if() {
        let mut env = GlobalEnv::new();
        env.set_value("t", Value::Bool(true));
        env.set_value("f", Value::Bool(false));

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

        env.set("f0", Rc::new(Value::fun0("f0", || 123)));
        eval_str("(f0)", &mut env).should_ok(123.into());
        eval_str("(f0 1)", &mut env).should_error(EvalError::ArgumentSize);

        env.set("f1", Rc::new(Value::fun1("f1", |n: i32| n)));
        eval_str("(f1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 1 2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f1 1)", &mut env).should_ok(1.into());

        env.set("f2", Rc::new(Value::fun2("f2", |n: i32, m: i32| n + m)));
        eval_str("(f2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f2 1 2)", &mut env).should_ok(3.into());

        env.set("sum", Rc::new(Value::fun_fold("sum", 0, |a, x| a + x)));
        eval_str("(sum)", &mut env).should_ok(0.into());
        eval_str("(sum 1)", &mut env).should_ok(1.into());
        eval_str("(sum 1 2)", &mut env).should_ok(3.into());
        eval_str("(sum 'x)", &mut env).should_error(EvalError::InvalidArg);

        env.set(
            "sum1",
            Rc::new(Value::fun_reduce("sum1", |a: i32, x: i32| a + x)),
        );
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
        eval_str("(-)", &mut env).should_ok(0.into());
        eval_str("(- 1)", &mut env).should_ok((-1).into());
        eval_str("(- 1 2)", &mut env).should_ok((-3).into());

        eval_str("(*)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(* 1)", &mut env).should_ok(1.into());
        eval_str("(* 1 2)", &mut env).should_ok(2.into());

        eval_str("(/)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(/ 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(/ 4 2)", &mut env).should_ok(2.into());

        eval_str("(%)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(% 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(% 4 2)", &mut env).should_ok(0.into());
    }

    // TODO: Floating point arithmetic
}
