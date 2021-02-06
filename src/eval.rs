use std::rc::Rc;

use crate::value::Extract;
use crate::value::RefValue;
use crate::value::Value;

use std::cell::RefCell;

mod error;
pub use error::EvalError;

mod global_env;
pub use global_env::GlobalEnv;

mod local_env;
pub use local_env::LocalEnv;

mod compile;

pub use compile::Ast;
pub use compile::TopAst;

pub type EvalResult = Result<Value, EvalError>;

pub fn eval(e: &Value, global: &mut GlobalEnv) -> EvalResult {
    let ast = compile::build_top_ast(e, global)?;
    eval_top(&ast, global)
}

fn eval_top(top: &TopAst, global: &mut GlobalEnv) -> EvalResult {
    match top {
        TopAst::Define(name, value) => {
            let value = eval_local_loop(value, global, None)?;
            global.set(name, value);
            Ok(Value::nil())
        }
        TopAst::Expr(value) => eval_local_loop(&value, global, None),
    }
}

enum Cont {
    Ret(Value),
    Cont(Value, Vec<Value>),
}

impl Cont {
    fn ok_ret(v: Value) -> Result<Cont, EvalError> {
        Ok(Cont::Ret(v))
    }
    fn ok_cont(f: Value, args: Vec<Value>) -> Result<Cont, EvalError> {
        Ok(Cont::Cont(f, args))
    }
}

fn illegal_argument_error<T>(value: Value) -> Result<T, EvalError> {
    Err(EvalError::IllegalArgument(value))
}

fn eval_local_loop(
    ast: &Ast,
    global: &mut GlobalEnv,
    local: Option<&Rc<RefCell<LocalEnv>>>,
) -> EvalResult {
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
) -> Result<Cont, EvalError> {
    match ast {
        Ast::Const(v) => Cont::ok_ret(v.clone()),
        Ast::GetGlobal(global_id) => Cont::ok_ret(global.get(*global_id).clone()),
        Ast::GetLocal(key) => {
            let value = local
                .expect("local env should exist")
                .borrow()
                .lookup(key)
                .expect("local should exist");
            Cont::ok_ret(value)
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
        Ast::Lambda {
            param_names,
            rest_name,
            bodies,
            expr,
        } => {
            let lambda = RefValue::Lambda {
                param_names: param_names.clone(),
                rest_name: rest_name.clone(),
                bodies: bodies.clone(),
                expr: expr.clone(),
                env: local.cloned(),
            };
            Cont::ok_ret(Value::ref_value(lambda))
        }
        Ast::Apply(f, args) => {
            let f = eval_local_loop(f, global, local)?;
            let mut arg_values = vec![];
            for arg in args.iter() {
                let a = eval_local_loop(arg, global, local)?;
                arg_values.push(a);
            }
            Cont::ok_cont(f, arg_values)
        }
        Ast::SetLocal {
            name,
            value,
            safe_only,
        } => {
            let value = eval_local_loop(value, global, local)?;
            if *safe_only && !value.is_cyclic_reference_safe() {
                return Err(EvalError::Unsafe);
            }
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
        Ast::SetGlobal { id, value, .. } => {
            let value = eval_local_loop(value, global, local)?;
            global.set_by_id(*id, value);
            Cont::ok_ret(Value::nil())
        }
        Ast::CatchError { handler, expr } => match eval_local_loop(expr, global, local) {
            Ok(value) => Cont::ok_ret(value),
            Err(err) => {
                let handler = eval_local_loop(handler, global, local)?;
                let (name, err) = err.to_tuple();
                eval_apply(&handler, &[Value::sym(name), err], global)
            }
        },
        Ast::Error(err) => Err(err.clone()),
    }
}

fn bind_args(
    param_names: &[Rc<str>],
    rest_name: Option<Rc<str>>,
    args: &[Value],
    parent: Option<Rc<RefCell<LocalEnv>>>,
) -> Result<LocalEnv, EvalError> {
    let invalid_argument_size = (rest_name.is_none() && param_names.len() != args.len())
        || (rest_name.is_some() && param_names.len() > args.len());
    if invalid_argument_size {
        illegal_argument_error(Value::list(args))
    } else {
        let mut values = std::collections::HashMap::new();
        for (k, v) in param_names.iter().zip(args) {
            values.insert(k.clone(), v.clone());
        }
        if let Some(rest_name) = rest_name {
            let rest = Value::list(&args[param_names.len()..]);
            values.insert(rest_name, rest);
        }

        Ok(LocalEnv::new(values, parent))
    }
}

fn eval_apply(f: &Value, args: &[Value], global: &mut GlobalEnv) -> Result<Cont, EvalError> {
    match f {
        Value::Ref(r) => match r.as_ref() {
            RefValue::Lambda {
                param_names,
                rest_name,
                bodies,
                expr,
                env,
            } => {
                let local = bind_args(param_names, rest_name.clone(), args, env.clone())?;
                let local = Rc::new(RefCell::new(local));
                for b in bodies.as_ref() {
                    eval_local_loop(b, global, Some(&local))?;
                }
                eval_local(expr, global, Some(&local))
            }
            RefValue::Fun { fun, .. } => fun.0(args).map(Cont::Ret),
            RefValue::Cons(..) => Err(EvalError::CantApply(
                f.clone(),
                args.iter().cloned().collect(),
            )),
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
    use crate::predef;

    fn eval_str(s: &str, env: &mut GlobalEnv) -> EvalResult {
        let expr = s.parse::<Value>().expect("should valid sexpr");
        eval(&expr, env)
    }

    trait Assertion {
        fn should_error(&self, err: EvalError);
        fn should_ok<T: Into<Value>>(&self, value: T);
        fn should_nil(&self);
    }
    impl Assertion for EvalResult {
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
        eval_str("'(1 2)", &mut env).should_ok(list![1, 2]);
        eval_str("(quote (1 2))", &mut env).should_ok(list![1, 2]);
        eval_str("(quote 1 . 2)", &mut env).should_error(EvalError::IllegalArgument(list![1; 2]));
        eval_str("(quote . 1)", &mut env).should_error(EvalError::IllegalArgument(1.into()));
        eval_str("(quote 1 2)", &mut env).should_error(EvalError::IllegalArgument(list![1, 2]));
    }

    #[test]
    fn test_define() {
        let mut env = GlobalEnv::new();

        eval_str("x", &mut env).should_error(EvalError::VariableNotFound("x".into()));
        eval_str("(define x 1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

        eval_str("(define x '1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

        eval_str("(define x 2 3)", &mut env).should_error(EvalError::IllegalArgument(list![
            Value::sym("x"),
            2,
            3
        ]));
        eval_str("(define 1 2)", &mut env).should_error(EvalError::SymbolRequired);
        eval_str("(define x aaa)", &mut env)
            .should_error(EvalError::VariableNotFound("aaa".into()));

        eval_str("(if 1 (define x 1) ())", &mut env).should_error(EvalError::DefineInLocalContext);
    }

    #[test]
    fn test_lambda_error() {
        let mut env = GlobalEnv::new();

        eval_str("(lambda)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(lambda () 1 . 2)", &mut env)
            .should_error(EvalError::IllegalArgument(list![list![], 1 ; 2]));
        eval_str("(lambda (x))", &mut env)
            .should_error(EvalError::IllegalArgument(list![list![Value::sym("x")]]));

        eval_str("(lambda 1 1)", &mut env).should_error(EvalError::SymbolRequired);
    }
    #[test]
    fn test_lambda_simple() {
        let mut env = GlobalEnv::new();

        eval_str("((lambda () 1))", &mut env).should_ok(1);
        eval_str("((lambda (x) x) 1)", &mut env).should_ok(1);
        eval_str("((lambda (x y) x) 1)", &mut env)
            .should_error(EvalError::IllegalArgument(list![1]));
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
        eval_str("(my-head)", &mut env).should_error(EvalError::IllegalArgument(list![]));
    }

    #[test]
    fn test_lambda_lookup_global() {
        let mut env = GlobalEnv::new();
        env.set("x", 1.into());

        eval_str("((lambda () x))", &mut env).should_ok(1);
    }

    #[test]
    fn test_if() {
        let mut env = predef();

        eval_str("(if true 1 2)", &mut env).should_ok(1);
        eval_str("(if false 1 2)", &mut env).should_ok(2);

        eval_str("(define x '(0))", &mut env).should_nil();
        eval_str("(if true (set-car! x 1) (set-car! x 2))", &mut env).should_ok(Value::Nil);
        eval_str("(car x)", &mut env).should_ok(1);

        eval_str("(if false (set-car! x 1) (set-car! x 2))", &mut env).should_ok(Value::Nil);
        eval_str("(car x)", &mut env).should_ok(2);
    }

    #[test]
    fn test_fun() {
        let mut env = GlobalEnv::new();

        env.set("f0", Value::fun0("f0", || 123));
        eval_str("(f0)", &mut env).should_ok(123);
        eval_str("(f0 1)", &mut env).should_error(EvalError::IllegalArgument(list![1]));

        env.set("f1", Value::fun1("f1", |n: i32| n));
        eval_str("(f1)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(f1 1 2)", &mut env).should_error(EvalError::IllegalArgument(list![1, 2]));
        eval_str("(f1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f1 1)", &mut env).should_ok(1);

        env.set("f2", Value::fun2("f2", |n: i32, m: i32| n + m));
        eval_str("(f2)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(f2 1)", &mut env).should_error(EvalError::IllegalArgument(list![1]));
        eval_str("(f2 1 2 3)", &mut env).should_error(EvalError::IllegalArgument(list![1, 2, 3]));
        eval_str("(f2 1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f2 1 2)", &mut env).should_ok(3);

        env.set("sum1", Value::fun_reduce("sum1", |a: i32, x: i32| a + x));
        eval_str("(sum1)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(sum1 'x)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(sum1 1)", &mut env).should_ok(1);
        eval_str("(sum1 1 2)", &mut env).should_ok(3);
    }

    #[test]
    fn test_predef_constants() {
        let mut env = predef();

        eval_str("true", &mut env).should_ok(Value::Bool(true));
        eval_str("false", &mut env).should_ok(Value::Bool(false));
    }

    #[test]
    fn test_predef_arithmetic() {
        let mut env = predef();

        eval_str("(+)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(+ 1)", &mut env).should_ok(1);
        eval_str("(+ 1 2)", &mut env).should_ok(3);

        // TODO: (-) should accept >= 1 argument
        eval_str("(-)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(- 1)", &mut env).should_ok(-1);
        eval_str("(- 3 8)", &mut env).should_ok(-5);

        eval_str("(*)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(* 1)", &mut env).should_ok(1);
        eval_str("(* 1 2)", &mut env).should_ok(2);

        eval_str("(/)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(/ 1)", &mut env).should_error(EvalError::IllegalArgument(list![1]));
        eval_str("(/ 4 2)", &mut env).should_ok(2);

        eval_str("(%)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(% 1)", &mut env).should_error(EvalError::IllegalArgument(list![1]));
        eval_str("(% 4 2)", &mut env).should_ok(0);
        // TODO: Floating point arithmetic
    }

    #[test]
    fn test_predef_eq() {
        let mut env = predef();

        eval_str("(eq? 1 1)", &mut env).should_ok(true);
        eval_str("(eq? 1 2)", &mut env).should_ok(false);

        eval_str("(eq? '(1 2 (3 4) . 5) '(1 2 (3 4) . 5))", &mut env).should_ok(true);

        eval_str("(eq? eq? eq?)", &mut env).should_ok(true);
        eval_str("(eq? eq? +)", &mut env).should_ok(false);
    }

    #[test]
    fn test_predef_cons() {
        let env = &mut predef();
        eval_str("(cons 1 2)", env).should_ok(Value::cons(1, 2));
        eval_str("(cons)", env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(cons 1 2 3)", env).should_error(EvalError::IllegalArgument(list![1, 2, 3]));
    }

    #[test]
    fn test_predef_list() {
        let env = &mut predef();
        eval_str("(list)", env).should_ok(Value::nil());
        eval_str("(list 1)", env).should_ok(list![1]);
        eval_str("(list 1 2)", env).should_ok(list![1, 2]);
    }

    #[test]
    fn test_complex_fib() {
        let mut env = predef();

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
        let env = &mut predef();

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
        let env = &mut predef();
        eval_str("(define global-var 1)", env).should_nil();

        eval_str("((lambda (x) (set-local! x 2) x) 1)", env).should_ok(2);
        eval_str("((lambda (x) (set-local! unk 1)) 1)", env)
            .should_error(EvalError::VariableNotFound("unk".into()));
        eval_str("((lambda (x) (set-local! global-var 1)) 1)", env)
            .should_error(EvalError::VariableNotFound("global-var".into()));

        eval_str("(((lambda (x) (lambda (y) (set-local! x 42) x)) 1) 2)", env).should_ok(42);

        eval_str("((lambda (x) (set-local! x '(1 2 3)) x) 1)", env).should_error(EvalError::Unsafe);
        eval_str("((lambda (x) (unsafe-set-local! x '(1 2 3)) x) 1)", env)
            .should_ok(list![1, 2, 3]);
    }

    #[test]
    fn test_set_local_counter() {
        let env = &mut predef();

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

    #[test]
    fn test_error() {
        let env = &mut predef();

        eval_str("(error 123)", env).should_error(EvalError::User(list![123]));
    }

    #[test]
    fn test_catch_error() {
        let env = &mut predef();
        eval_str(
            "
            (catch-error
                (lambda (e x) (list 'error e x))
                (error 123))",
            env,
        )
        .should_ok(list![Value::sym("error"), Value::sym("User"), list![123]]);
        eval_str(
            "
            (catch-error
                (lambda (e x) (list 'error e x))
                (+ 1 2))",
            env,
        )
        .should_ok(3);
        eval_str(
            "
            (catch-error
                (lambda (e x) (list 'error e x))
                aaa)",
            env,
        )
        .should_ok(list![
            Value::sym("error"),
            Value::sym("VariableNotFound"),
            list![Value::sym("aaa")]
        ]);
    }

    #[test]
    fn test_assert_eq() {
        let env = &mut predef();

        eval_str("(assert-eq 1 1)", env).should_nil();
        eval_str("(assert-eq 1 2)", env).should_error(EvalError::User(list![
            Value::sym("assert-eq"),
            1,
            2
        ]));
    }
}
