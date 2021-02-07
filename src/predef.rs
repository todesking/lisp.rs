use crate::eval::EvalError;
use crate::eval::GlobalEnv;
use crate::eval_str_or_panic;
use crate::value::Extract;
use crate::value::Value;
pub fn load(global: &mut GlobalEnv) {
    global.set("true", Value::Bool(true));
    global.set("false", Value::Bool(false));

    global.set_fun("error", |args| {
        Err(EvalError::User(Value::list(args.iter())))
    });

    global.set("+", Value::fun_reduce("+", |l: i32, r: i32| l + r));
    global.set_fun("-", |args| {
        let mut it = args.iter();
        let x0 = it.next().ok_or_else(|| EvalError::illegal_argument(args))?;
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
    global.set_fun2("eq?", |lhs, rhs| Ok(Value::bool(lhs == rhs)));

    global.set(
        "cons",
        Value::fun("cons", |args| {
            let mut it = args.iter();
            let x1 = it.next().ok_or_else(|| EvalError::illegal_argument(args))?;
            let x2 = it.next().ok_or_else(|| EvalError::illegal_argument(args))?;
            if it.next() == None {
                Ok(Value::cons(x1.clone(), x2.clone()))
            } else {
                Err(EvalError::illegal_argument(args))
            }
        }),
    );
    eval_str_or_panic("(define list (lambda x x))", global);
    global.set_fun1("car", |x1| {
        if let Some((car, _)) = x1.to_cons() {
            Ok(car)
        } else {
            Err(EvalError::InvalidArg)
        }
    });
    global.set_fun1("cdr", |x1| {
        if let Some((_, cdr)) = x1.to_cons() {
            Ok(cdr)
        } else {
            Err(EvalError::InvalidArg)
        }
    });
    global.set_fun2("set-car!", |x, v| x.set_car(v.clone(), true));
    global.set_fun2("set-cdr!", |x, v| x.set_cdr(v.clone(), true));
    global.set_fun2("unsafe-set-car!", |x, v| x.set_car(v.clone(), false));
    global.set_fun2("unsafe-set-cdr!", |x, v| x.set_cdr(v.clone(), false));

    eval_str_or_panic(
        "
            (define assert-eq
                (lambda (expected actual)
                    (if (eq? expected actual) () (error 'assert-eq expected actual))))",
        global,
    );
    eval_str_or_panic(
        "(define assert-error
                (lambda (f err)
                    (assert-eq
                        (catch-error
                            (lambda (err x) (cons err x))
                            (f))
                        err)))",
        global,
    );
}
