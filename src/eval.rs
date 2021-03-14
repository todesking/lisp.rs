use std::rc::Rc;

use crate::local_env::LocalEnv;
use crate::value::Extract;
use crate::value::RefValue;
use crate::GlobalEnv;
use crate::GlobalWrite;
use crate::Value;

use std::cell::RefCell;

use crate::ast::Ast;
use crate::ast::QuasiQuote;
use crate::build_top_ast;
use crate::compile::build_top_ast_within_module;
use crate::EvalError;
use crate::TopAst;

pub type EvalResult = Result<Value, EvalError>;

pub fn eval<'v, 'g>(e: &Value, global: &mut impl GlobalWrite<'g>) -> EvalResult {
    let ast = build_top_ast(e, global.as_ref())?;
    eval_top_ast(&ast, global)
}

type Args = Rc<RefCell<Vec<Value>>>;

pub fn eval_top_ast<'v, 'g>(top: &'v TopAst, global: &mut impl GlobalWrite<'g>) -> EvalResult {
    let args = Rc::new(RefCell::new(Vec::new()));
    match top {
        TopAst::Begin(asts) => {
            let mut value = Value::Nil;
            for ast in asts {
                value = eval_top_ast(ast, global)?;
            }
            Ok(value)
        }
        TopAst::Define(abs_name, value) => {
            let (mname, name) = abs_name.split();
            global
                .define_module_member(mname, name)
                .ok_or_else(|| EvalError::ReadOnly(abs_name.to_string()))?;
            global
                .set(abs_name.clone(), Value::nil())
                .ok_or_else(|| EvalError::ReadOnly(abs_name.to_string()))?;
            let value = eval_local_loop(value, global, &None, &args)?;
            global
                .set(abs_name.clone(), value)
                .ok_or_else(|| EvalError::ReadOnly(abs_name.to_string()))?;
            Ok(Value::nil())
        }
        TopAst::DefMacro(abs_name, value) => {
            let value = eval_local_loop(value, global, &None, &args)?;
            global
                .set_macro(abs_name.clone(), value)
                .ok_or_else(|| EvalError::ReadOnly(abs_name.to_string()))?;
            let (mname, name) = abs_name.split();
            global.define_module_member(mname, name);
            Ok(Value::nil())
        }
        TopAst::DefModule(abs_name) => {
            let (mname, name) = abs_name.split();
            global
                .define_module_member(mname, name)
                .map(|_| Value::Nil)
                .ok_or_else(|| EvalError::ReadOnly(abs_name.to_string()))
        }
        TopAst::Import(name, absname) => global
            .import(name.clone(), absname.clone())
            .map(|_| Value::Nil)
            .ok_or_else(|| EvalError::ReadOnly("import table".to_owned())),
        TopAst::Expr(value) => eval_local_loop(&value, global, &None, &args),
        TopAst::Delay(current_module, value) => {
            let value =
                build_top_ast_within_module(value, global.as_ref(), current_module.clone())?;
            eval_top_ast(&value, global)
        }
    }
}

enum Cont {
    Ret(Value),
    Cont(Value, Vec<Value>),
}

impl Cont {
    #[allow(clippy::unnecessary_wraps)]
    fn ok_ret(v: Value) -> Result<Cont, EvalError> {
        Ok(Cont::Ret(v))
    }
    #[allow(clippy::unnecessary_wraps)]
    fn ok_cont(f: Value, args: Vec<Value>) -> Result<Cont, EvalError> {
        Ok(Cont::Cont(f, args))
    }
}

fn eval_local_loop<'g>(
    ast: &Ast,
    global: &mut impl GlobalWrite<'g>,
    local: &Option<Rc<LocalEnv>>,
    args: &Args,
) -> EvalResult {
    let cont = eval_local(ast, global, local, args)?;
    unwrap_cont(cont, global)
}

fn unwrap_cont<'g>(cont: Cont, global: &mut impl GlobalWrite<'g>) -> EvalResult {
    let mut cont = cont;
    loop {
        match cont {
            Cont::Ret(v) => return Ok(v),
            Cont::Cont(f, args) => cont = eval_apply(&f, args, global)?,
        }
    }
}

pub fn eval_macro(lambda: &Value, args: Vec<Value>, global: &GlobalEnv) -> EvalResult {
    let mut global = global.read_only();
    let macro_err = |err| EvalError::Macro(Box::new(err));
    let cont = eval_apply(lambda, args, &mut global).map_err(macro_err)?;
    unwrap_cont(cont, &mut global).map_err(macro_err)
}

fn eval_local<'g>(
    ast: &Ast,
    global: &mut impl GlobalWrite<'g>,
    local: &Option<Rc<LocalEnv>>,
    args: &Args,
) -> Result<Cont, EvalError> {
    match ast {
        Ast::Const(v) => Cont::ok_ret(v.clone()),
        Ast::GetGlobal(_, global_id) => Cont::ok_ret(global.as_ref().get(*global_id).clone()),
        Ast::GetLocal(_, depth, index) => {
            let value = LocalEnv::get(local, *depth, *index);
            Cont::ok_ret(value)
        }
        Ast::GetArgument(_, index) => Cont::ok_ret(args.borrow()[*index].clone()),
        Ast::If(cond, th, el) => {
            let cond = eval_local_loop(cond, global, local, args)?;
            if let Some(b) = bool::extract(&cond) {
                let value = if b { th } else { el };
                eval_local(value, global, local, args)
            } else {
                Err(EvalError::InvalidArg)
            }
        }
        Ast::Lambda {
            param_names,
            rest_name,
            depth,
            bodies,
            expr,
        } => {
            let lambda = RefValue::Lambda {
                param_names: param_names.clone(),
                rest_name: rest_name.clone(),
                bodies: bodies.clone(),
                expr: expr.clone(),
                env: LocalEnv::extended(local.clone(), *depth, args.clone()),
            };
            Cont::ok_ret(Value::ref_value(lambda))
        }
        Ast::Apply(f, new_args) => {
            let f = eval_local_loop(f, global, local, args)?;
            let mut arg_values = vec![];
            for arg in new_args.iter() {
                let a = eval_local_loop(arg, global, local, args)?;
                arg_values.push(a);
            }
            Cont::ok_cont(f, arg_values)
        }
        Ast::SetLocal {
            depth,
            index,
            value,
            ..
        } => {
            let value = eval_local_loop(value, global, local, args)?;
            LocalEnv::set(local, *depth, *index, value);
            Cont::ok_ret(Value::nil())
        }
        Ast::SetGlobal { id, value, name } => {
            let value = eval_local_loop(value, global, local, args)?;
            global
                .set_by_id(*id, value)
                .ok_or_else(|| EvalError::ReadOnly(name.to_owned()))?;
            Cont::ok_ret(Value::nil())
        }
        Ast::SetArg { index, value, .. } => {
            args.borrow_mut()[*index] = eval_local_loop(value, global, local, args)?;
            Cont::ok_ret(Value::nil())
        }
        Ast::EnsureSafe(value) => {
            let value = eval_local_loop(value, global, local, args)?;
            if !value.is_cyclic_reference_safe() {
                Err(EvalError::Unsafe)
            } else {
                Cont::ok_ret(value)
            }
        }
        Ast::CatchError { handler, expr } => match eval_local_loop(expr, global, local, args) {
            Ok(value) => Cont::ok_ret(value),
            Err(err) => {
                let handler = eval_local_loop(handler, global, local, args)?;
                let (name, err) = err.to_tuple();
                let args = vec![Value::sym(name), err];
                eval_apply(&handler, args, global)
            }
        },
        Ast::Error(err) => Err(err.clone()),
        Ast::GetRec(_, depth, index) => Cont::ok_ret(LocalEnv::get_rec(local, *depth, *index)),
        Ast::LetRec {
            rec_depth,
            local_depth,
            defs,
            body,
            expr,
        } => {
            let local = Some(LocalEnv::rec_extended(
                local.clone(),
                *rec_depth,
                *local_depth,
                defs,
                args.clone(),
            ));
            for b in body {
                eval_local_loop(b, global, &local, args)?;
            }
            eval_local(expr, global, &local, args)
        }
        Ast::QuasiQuote(qq) => eval_quasiquote(qq, global, local, args).map(Cont::Ret),
        Ast::IfMatch(varsize, expr, pat, th, el) => {
            let expr = eval_local_loop(expr, global, local, args)?;
            let mut vars = Vec::with_capacity(*varsize);
            if pat.match_and_bind(&expr, &mut vars) {
                let th = eval_local_loop(th, global, local, args)?;
                Cont::ok_cont(th, vars)
            } else {
                eval_local(&el, global, local, args)
            }
        }
    }
}

fn eval_quasiquote<'g>(
    qq: &QuasiQuote,
    global: &mut impl GlobalWrite<'g>,
    local: &Option<Rc<LocalEnv>>,
    args: &Args,
) -> EvalResult {
    match qq {
        QuasiQuote::Const(value) => Ok(value.clone()),
        QuasiQuote::Expr(ast) => eval_local_loop(ast, global, local, args),
        QuasiQuote::Cons(car, cdr) => {
            let car = eval_quasiquote(car, global, local, args)?;
            let cdr = eval_quasiquote(cdr, global, local, args)?;
            Ok(Value::cons(car, cdr))
        }
        QuasiQuote::Append(expr, list) => {
            let l1 = eval_local_loop(expr, global, local, args)?;
            let l2 = eval_quasiquote(list, global, local, args)?;
            append_list(l1, l2).ok_or(EvalError::QuasiQuote)
        }
    }
}

fn append_list(l1: Value, l2: Value) -> Option<Value> {
    let l1 = l1.to_vec()?;
    Some(l1.into_iter().rev().fold(l2, |a, x| Value::cons(x, a)))
}

fn bind_args(param_count: usize, has_rest: bool, mut args: Vec<Value>) -> Result<Args, EvalError> {
    if has_rest {
        if args.len() < param_count {
            Err(EvalError::illegal_argument(&args))
        } else {
            let rest = Value::list(args[param_count..].to_vec().iter());
            args.truncate(param_count);
            args.push(rest);
            Ok(Rc::new(RefCell::new(args)))
        }
    } else if args.len() != param_count {
        Err(EvalError::illegal_argument(&args))
    } else {
        Ok(Rc::new(RefCell::new(args)))
    }
}

fn eval_apply<'g>(
    f: &Value,
    args: Vec<Value>,
    global: &mut impl GlobalWrite<'g>,
) -> Result<Cont, EvalError> {
    match f {
        Value::Ref(r) => match &**r {
            RefValue::Lambda {
                param_names,
                rest_name,
                bodies,
                expr,
                env,
            } => {
                // TODO: Make eval_*(env: &Option<Rc<LocalEnv>>) to env: Option<&Rc<LocalEnv>>
                let env = Some(env.clone());
                let args = bind_args(param_names.len(), rest_name.is_some(), args)?;
                for b in &**bodies {
                    eval_local_loop(b, global, &env, &args)?;
                }
                eval_local(expr, global, &env, &args)
            }
            RefValue::RecLambda { lambda_def, env } => {
                let args = bind_args(
                    lambda_def.param_names.len(),
                    lambda_def.rest_name.is_some(),
                    args,
                )?;
                let env = Some(env.clone());
                for b in &*lambda_def.bodies {
                    eval_local_loop(b, global, &env, &args)?;
                }
                eval_local(&lambda_def.expr, global, &env, &args)
            }
            RefValue::Fun { fun, .. } => fun.0(&args).map(Cont::Ret),
            RefValue::GlobalFun { fun, .. } => fun.0(&args, global.as_ref()).map(Cont::Ret),
            RefValue::Cons(..) => Err(EvalError::CantApply(f.clone(), args.into_boxed_slice())),
        },
        _ => Err(EvalError::CantApply(f.clone(), args.into_boxed_slice())),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::predef;

    fn eval_str<'g>(s: &str, env: &mut impl GlobalWrite<'g>) -> EvalResult {
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

    // TODO
    fn abs_name(src: &str) -> crate::ast::AbsName {
        crate::ast::AbsName::new(
            src.split(':').collect::<Vec<_>>()[1..]
                .iter()
                .map(|&n| crate::ast::SimpleName::from(n).unwrap())
                .collect::<Vec<_>>(),
        )
    }

    #[test]
    fn test_sym() {
        let mut env = GlobalEnv::new();
        env.set(abs_name(":global:x"), 123.into());

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
        eval_str("(__define x 1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

        eval_str("(__define x '1)", &mut env).should_ok(Value::Nil);
        eval_str("x", &mut env).should_ok(1);

        eval_str("(__define x 2 3)", &mut env).should_error(EvalError::IllegalArgument(list![
            Value::sym("x"),
            2,
            3
        ]));
        eval_str("(__define 1 2)", &mut env).should_error(EvalError::SymbolRequired);
        eval_str("(__define x aaa)", &mut env)
            .should_error(EvalError::VariableNotFound("aaa".into()));

        eval_str("(if 1 (__define x 1) ())", &mut env)
            .should_error(EvalError::DefineInLocalContext);

        eval_str("(__define loop loop)", &mut env).should_nil();
        eval_str("loop", &mut env).should_nil();
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

        eval_str("(__define my-list (lambda x x))", &mut env).should_ok(Value::Nil);
        eval_str("(my-list 1 2 3)", &mut env).should_ok(list!(1, 2, 3));
        eval_str("(my-list)", &mut env).should_ok(list!());

        eval_str("(__define my-head (lambda (x . xs) x))", &mut env).should_ok(Value::Nil);
        eval_str("(__define my-tail (lambda (x . xs) xs))", &mut env).should_ok(Value::Nil);
        eval_str("(my-head 1)", &mut env).should_ok(1);
        eval_str("(my-tail 1)", &mut env).should_ok(list!());
        eval_str("(my-head 1 2)", &mut env).should_ok(1);
        eval_str("(my-tail 1 2)", &mut env).should_ok(list!(2));
        eval_str("(my-head)", &mut env).should_error(EvalError::IllegalArgument(list![]));
    }

    #[test]
    fn test_lambda_lookup_global() {
        let mut env = GlobalEnv::new();
        env.set(abs_name(":global:x"), 1.into());

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

        env.set(abs_name(":global:f0"), Value::fun0(":global:f0", || 123));
        eval_str("(f0)", &mut env).should_ok(123);
        eval_str("(f0 1)", &mut env).should_error(EvalError::IllegalArgument(list![1]));

        env.set(abs_name(":global:f1"), Value::fun1("f1", |n: i32| n));
        eval_str("(f1)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(f1 1 2)", &mut env).should_error(EvalError::IllegalArgument(list![1, 2]));
        eval_str("(f1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f1 1)", &mut env).should_ok(1);

        env.set(
            abs_name(":global:f2"),
            Value::fun2("f2", |n: i32, m: i32| n + m),
        );
        eval_str("(f2)", &mut env).should_error(EvalError::IllegalArgument(list![]));
        eval_str("(f2 1)", &mut env).should_error(EvalError::IllegalArgument(list![1]));
        eval_str("(f2 1 2 3)", &mut env).should_error(EvalError::IllegalArgument(list![1, 2, 3]));
        eval_str("(f2 1 'a)", &mut env).should_error(EvalError::InvalidArg);
        eval_str("(f2 1 2)", &mut env).should_ok(3);

        env.set(
            abs_name(":global:sum1"),
            Value::fun_reduce("sum1", |a: i32, x: i32| a + x),
        );
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

    #[test]
    fn test_module() {
        let env = &mut predef();
        eval_str("(module ::m1 123)", env)
            .should_error(EvalError::IllegalArgument(list!["::m1", 123]));
        eval_str("(module m1::m2 123)", env)
            .should_error(EvalError::IllegalArgument(list!["m1::m2", 123]));
    }

    #[test]
    fn test_import() {
        let env = &mut predef();
        eval_str("(module m1 (:global:define x 1))", env).should_nil();
        eval_str("(import-from m1 x)", env).should_nil();
        eval_str("x", env).should_ok(1);
        eval_str("(import-from xxx x)", env)
            .should_error(EvalError::ModuleNotFound(":xxx".to_owned()));
        eval_str("(import-from m1 y)", env).should_error(EvalError::IllegalArgument(list!["y"]));
    }
}
