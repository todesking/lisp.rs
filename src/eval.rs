use std::rc::Rc;

use crate::global_env::GlobalEnv;
use crate::local_env::LocalEnv;
use crate::value::Extract;
use crate::value::RefValue;
use crate::value::Value;

use std::cell::RefCell;

#[derive(Debug, PartialEq, Eq)]
pub enum EvalError {
    VariableNotFound(String),
    ImproperArgs,
    ArgumentSize,
    SymbolRequired,
    InvalidArg,
    CantApply(Value, Box<[Value]>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ast {
    Const(Value),
    Define(String, Box<Ast>),
    Lookup(String),
    If(Box<Ast>, Box<Ast>, Box<Ast>),
    Lambda(Vec<Rc<str>>, Option<Rc<str>>, Rc<[Ast]>),
    Apply(Box<Ast>, Vec<Ast>),
    SetLocal(String, Box<Ast>),
}

pub fn build_ast(expr: &Value) -> std::result::Result<Ast, EvalError> {
    match expr {
        Value::Int(n) => Ok(Ast::Const(Value::int(*n))),
        Value::Bool(v) => Ok(Ast::Const(Value::bool(*v))),
        Value::Nil => Ok(Ast::Const(Value::nil())),
        Value::Sym(key) => Ok(Ast::Lookup(key.to_string())),
        Value::Cons(car, cdr) => match car.as_ref() {
            Value::Sym(name) if name.as_ref() == "quote" => match cdr.as_ref().to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [x] => Ok(Ast::Const(x.as_ref().clone())),
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name.as_ref() == "define" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [name, value] => match name.as_ref() {
                        Value::Sym(name) => {
                            let value = build_ast(value)?;
                            Ok(Ast::Define(name.to_string(), Box::new(value)))
                        }
                        _ => Err(EvalError::SymbolRequired),
                    },
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name.as_ref() == "if" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [cond, th, el] => {
                        let cond = build_ast(cond)?;
                        let th = build_ast(th)?;
                        let el = build_ast(el)?;
                        Ok(Ast::If(Box::new(cond), Box::new(th), Box::new(el)))
                    }
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            Value::Sym(name) if name.as_ref() == "lambda" => match cdr.as_ref() {
                Value::Cons(params, body) => {
                    let (param_names, rest_name) = params.collect_improper(|v| match v {
                        Value::Sym(name) => Ok(name.clone()),
                        _ => Err(EvalError::SymbolRequired),
                    })?;
                    match body.to_vec() {
                        None => Err(EvalError::ImproperArgs),
                        Some(body) => match body.as_slice() {
                            [] => Err(EvalError::ArgumentSize),
                            body => {
                                let body =
                                    body.iter()
                                        .map(|v| build_ast(v.as_ref()))
                                        .collect::<std::result::Result<Rc<[Ast]>, EvalError>>()?;
                                Ok(Ast::Lambda(param_names, rest_name, body))
                            }
                        },
                    }
                }
                Value::Nil => Err(EvalError::ArgumentSize),
                _ => Err(EvalError::ImproperArgs),
            },
            Value::Sym(name) if name.as_ref() == "set-local!" => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => match args.as_slice() {
                    [name, expr] => {
                        let name = name.as_ref().as_sym().ok_or(EvalError::SymbolRequired)?;
                        let expr = build_ast(expr)?;
                        Ok(Ast::SetLocal(name.to_string(), Box::new(expr)))
                    }
                    _ => Err(EvalError::ArgumentSize),
                },
            },
            f => match cdr.to_vec() {
                None => Err(EvalError::ImproperArgs),
                Some(args) => {
                    let f = build_ast(f)?;
                    let mut arg_values = Vec::with_capacity(args.len());
                    for arg in args.iter() {
                        let arg = build_ast(arg)?;
                        arg_values.push(arg);
                    }
                    Ok(Ast::Apply(Box::new(f), arg_values))
                }
            },
        },
        Value::Ref(r) => match r.as_ref() {
            RefValue::Lambda { .. } => unimplemented!(),
            RefValue::Fun { .. } => unimplemented!(),
        },
    }
}

pub type Result = std::result::Result<Value, EvalError>;

pub fn eval(e: &Value, global: &mut GlobalEnv) -> Result {
    let ast = build_ast(e)?;
    eval_local_loop(&ast, global, None)
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

fn eval_local_loop(
    ast: &Ast,
    global: &mut GlobalEnv,
    local: Option<&Rc<RefCell<LocalEnv>>>,
) -> Result {
    let mut res = eval_local(ast, global, local)?;
    loop {
        match res {
            Cont::Ret(v) => return Ok(v),
            Cont::Cont(f, args) => res = eval_apply(&f, args.as_ref(), global)?,
        }
    }
}

fn eval_local(
    ast: &Ast,
    global: &mut GlobalEnv,
    local: Option<&Rc<RefCell<LocalEnv>>>,
) -> std::result::Result<Cont, EvalError> {
    match ast {
        Ast::Const(v) => Cont::ok_ret(v.clone()),
        Ast::Lookup(key) => local
            .map_or_else(
                || global.lookup(key),
                |l| match l.borrow().lookup(key) {
                    None => global.lookup(key),
                    found @ Some(_) => found,
                },
            )
            .map(Cont::Ret)
            .ok_or_else(|| EvalError::VariableNotFound(key.to_string())),
        Ast::Define(name, value) => {
            let value = eval_local_loop(value, global, local)?;
            global.set(name, value);
            Cont::ok_ret(Value::nil())
        }
        Ast::If(cond, th, el) => {
            let cond = eval_local_loop(cond, global, local)?;
            if let Some(b) = bool::extract(&cond) {
                let value = if b { th } else { el };
                eval_local(value, global, local)
            } else {
                Err(EvalError::InvalidArg)
            }
        }
        Ast::Lambda(param_names, rest_name, body) => eval_lambda(
            param_names.clone(),
            rest_name.clone(),
            body.clone(),
            local.cloned(),
        ),
        Ast::Apply(f, args) => {
            let f = eval_local_loop(f, global, local)?;
            let mut arg_values = vec![];
            for arg in args.iter() {
                let a = eval_local_loop(arg, global, local)?;
                arg_values.push(a);
            }
            Cont::ok_cont(f, arg_values)
        }
        Ast::SetLocal(name, value) => {
            let value = eval_local_loop(value, global, local)?;
            local.map_or_else(
                || Err(EvalError::VariableNotFound(name.clone())),
                |l| {
                    if l.borrow_mut().set_if_defined(name, value) {
                        Cont::ok_ret(Value::nil())
                    } else {
                        Err(EvalError::VariableNotFound(name.clone()))
                    }
                },
            )
        }
    }
}

fn eval_lambda(
    param_names: Vec<Rc<str>>,
    rest_name: Option<Rc<str>>,
    body: Rc<[Ast]>,
    local: Option<Rc<RefCell<LocalEnv>>>,
) -> std::result::Result<Cont, EvalError> {
    Cont::ok_ret(Value::lambda(param_names, rest_name, body, local))
}

fn bind_args(
    param_names: &[Rc<str>],
    rest_name: Option<Rc<str>>,
    args: &[Value],
    parent: Option<Rc<RefCell<LocalEnv>>>,
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
                let local = Rc::new(RefCell::new(local));
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
        _ => Err(EvalError::CantApply(
            f.clone(),
            args.iter().cloned().collect(),
        )),
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
        fn should_ok<T: Into<Value>>(&self, value: T);
        fn should_nil(&self);
    }
    impl Assertion for Result {
        fn should_error(&self, err: EvalError) {
            assert_eq!(self, &Err(err));
        }
        fn should_ok<T: Into<Value>>(&self, value: T) {
            assert_eq!(self, &Ok(value.into()));
        }
        fn should_nil(&self) {
            self.should_ok(Value::nil());
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
        eval_str("1", &mut env).should_ok(1);
    }

    #[test]
    fn test_sym() {
        let mut env = GlobalEnv::new();
        env.set("x".to_string(), 123.into());

        eval_str("x", &mut env).should_ok(123);
    }

    #[test]
    fn test_nil() {
        let mut env = GlobalEnv::new();
        eval_str("()", &mut env).should_ok(Value::Nil);
    }

    #[test]
    fn test_quote() {
        let mut env = GlobalEnv::new();

        eval_str("'1", &mut env).should_ok(1);
        eval_str("'(1 2)", &mut env).should_ok(&vec![1, 2]);
        eval_str("(quote (1 2))", &mut env).should_ok(&vec![1, 2]);
        eval_str("(quote 1 . 2)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote . 1)", &mut env).should_error(EvalError::ImproperArgs);
        eval_str("(quote 1 2)", &mut env).should_error(EvalError::ArgumentSize);
    }

    #[test]
    fn test_define() {
        let mut env = GlobalEnv::new();

        eval_str("x", &mut env).should_error(EvalError::VariableNotFound("x".into()));
        eval_str("(define x 1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

        eval_str("(define x '1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

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

        eval_str("((lambda () 1))", &mut env).should_ok(1);
        eval_str("((lambda (x) x) 1)", &mut env).should_ok(1);
        eval_str("((lambda (x y) x) 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("((lambda (x y) y) 1 2)", &mut env).should_ok(2);
    }

    #[test]
    fn test_lambda_closure() {
        let mut env = GlobalEnv::new();

        eval_str("(((lambda (x) (lambda (y) y)) 1) 2)", &mut env).should_ok(2);
        eval_str("(((lambda (x) (lambda (y) x)) 1) 2)", &mut env).should_ok(1);
    }

    #[test]
    fn test_lambda_varargs() {
        let mut env = GlobalEnv::new();

        eval_str("(define my-list (lambda x x))", &mut env).should_ok(Value::Nil);
        eval_str("(my-list 1 2 3)", &mut env).should_ok(list!(1, 2, 3));
        eval_str("(my-list)", &mut env).should_ok(list!());

        eval_str("(define my-head (lambda (x . xs) x))", &mut env).should_ok(Value::Nil);
        eval_str("(define my-tail (lambda (x . xs) xs))", &mut env).should_ok(Value::Nil);
        eval_str("(my-head 1)", &mut env).should_ok(1);
        eval_str("(my-tail 1)", &mut env).should_ok(list!());
        eval_str("(my-head 1 2)", &mut env).should_ok(1);
        eval_str("(my-tail 1 2)", &mut env).should_ok(list!(2));
        eval_str("(my-head)", &mut env).should_error(EvalError::ArgumentSize);
    }

    #[test]
    fn test_lambda_lookup_global() {
        let mut env = GlobalEnv::new();
        env.set("x", 1.into());

        eval_str("((lambda () x))", &mut env).should_ok(1);
    }

    #[test]
    fn test_if() {
        let mut env = GlobalEnv::new();
        env.set("t", Value::Bool(true));
        env.set("f", Value::Bool(false));

        eval_str("(if t 1 2)", &mut env).should_ok(1);
        eval_str("(if f 1 2)", &mut env).should_ok(2);

        eval_str("(if t (define x 1) (define x 2))", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

        eval_str("(if f (define x 1) (define x 2))", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(2);
    }

    #[test]
    fn test_fun() {
        let mut env = GlobalEnv::new();

        env.set("f0", Value::fun0("f0", || 123));
        eval_str("(f0)", &mut env).should_ok(123);
        eval_str("(f0 1)", &mut env).should_error(EvalError::ArgumentSize);

        env.set("f1", Value::fun1("f1", |n: i32| n));
        eval_str("(f1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 1 2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f1 1)", &mut env).should_ok(1);

        env.set("f2", Value::fun2("f2", |n: i32, m: i32| n + m));
        eval_str("(f2)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 2 3)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(f2 1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f2 1 2)", &mut env).should_ok(3);

        env.set("sum", Value::fun_fold("sum", 0, |a, x| a + x));
        eval_str("(sum)", &mut env).should_ok(0);
        eval_str("(sum 1)", &mut env).should_ok(1);
        eval_str("(sum 1 2)", &mut env).should_ok(3);
        eval_str("(sum 'x)", &mut env).should_error(EvalError::InvalidArg);

        env.set("sum1", Value::fun_reduce("sum1", |a: i32, x: i32| a + x));
        eval_str("(sum1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(sum1 'x)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(sum1 1)", &mut env).should_ok(1);
        eval_str("(sum1 1 2)", &mut env).should_ok(3);
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
        eval_str("(+ 1)", &mut env).should_ok(1);
        eval_str("(+ 1 2)", &mut env).should_ok(3);

        // TODO: (-) should accept >= 1 argument
        eval_str("(-)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(- 1)", &mut env).should_ok(-1);
        eval_str("(- 3 8)", &mut env).should_ok(-5);

        eval_str("(*)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(* 1)", &mut env).should_ok(1);
        eval_str("(* 1 2)", &mut env).should_ok(2);

        eval_str("(/)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(/ 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(/ 4 2)", &mut env).should_ok(2);

        eval_str("(%)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(% 1)", &mut env).should_error(EvalError::ArgumentSize);
        eval_str("(% 4 2)", &mut env).should_ok(0);
        // TODO: Floating point arithmetic
    }

    #[test]
    fn test_predef_eq() {
        let mut env = GlobalEnv::predef();

        eval_str("(eq? 1 1)", &mut env).should_ok(true);
        eval_str("(eq? 1 2)", &mut env).should_ok(false);

        eval_str("(eq? '(1 2 (3 4) . 5) '(1 2 (3 4) . 5))", &mut env).should_ok(true);

        eval_str("(eq? eq? eq?)", &mut env).should_ok(true);
        eval_str("(eq? eq? +)", &mut env).should_ok(false);
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
        .should_nil();
        eval_str("(fib 0)", &mut env).should_ok(0);
        eval_str("(fib 1)", &mut env).should_ok(1);
        eval_str("(fib 2)", &mut env).should_ok(1);
        eval_str("(fib 3)", &mut env).should_ok(2);
        eval_str("(fib 4)", &mut env).should_ok(3);
        eval_str("(fib 5)", &mut env).should_ok(5);
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

    #[test]
    fn test_set_local() {
        let env = &mut GlobalEnv::predef();

        eval_str(
            "
        (define make-counter
            (lambda ()
                ((lambda (c)
                    (lambda ()
                        (set-local! c (+ c 1))
                        (- c 1)))
                  0)))",
            env,
        )
        .should_nil();
        eval_str("(define c1 (make-counter))", env).should_nil();
        eval_str("(define c2 (make-counter))", env).should_nil();

        eval_str("(c1)", env).should_ok(0);

        eval_str("(c2)", env).should_ok(0);

        eval_str("(c1)", env).should_ok(1);
        eval_str("(c1)", env).should_ok(2);

        eval_str("(c2)", env).should_ok(1);
    }
}
