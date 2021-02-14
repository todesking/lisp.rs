use crate::eval::EvalError;
use crate::eval::GlobalEnv;
use crate::value::Extract;
use crate::value::Value;
use std::rc::Rc;

pub fn load(global: &mut GlobalEnv) {
    global.set("true", Value::Bool(true));
    global.set("false", Value::Bool(false));
    global.set_fun2("eq?", |lhs, rhs| Ok(Value::bool(lhs == rhs)));

    global.set_fun("error", |args| {
        Err(EvalError::User(Value::list(args.iter())))
    });

    global.set_fun("make-symbol", |args| {
        if args.len() != 1 {
            return Err(EvalError::illegal_argument(args));
        }
        if let Some(s) = args[0].as_str() {
            Ok(Value::Sym(s.clone()))
        } else {
            Err(EvalError::illegal_argument(args))
        }
    });

    global.set_fun1("to-string", |v| {
        let content = match v {
            Value::Sym(v) | Value::Str(v) => v.clone(),
            Value::Int(v) => Rc::from(v.to_string()),
            Value::Bool(v) => Rc::from(v.to_string()),
            _ => return Err(EvalError::illegal_argument(&[v.clone()])),
        };
        Ok(Value::Str(content))
    });
    global.set_fun("str-+", |args| {
        let args = args
            .iter()
            .map(|v| match v {
                Value::Str(v) => Ok(v.as_ref()),
                _ => Err(EvalError::illegal_argument(args)),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Value::Str(Rc::from(args.join(""))))
    });

    load_arithmetic(global);
    load_list_ops(global);
    load_from_str(include_str!("predef.lisp"), global);
}

fn load_arithmetic(global: &mut GlobalEnv) {
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
    global.set("<", Value::fun2("<", |l: i32, r: i32| l < r));
    global.set("<=", Value::fun2("<=", |l: i32, r: i32| l <= r));
    global.set(">", Value::fun2(">", |l: i32, r: i32| l > r));
    global.set(">=", Value::fun2(">=", |l: i32, r: i32| l >= r));
}

fn load_list_ops(global: &mut GlobalEnv) {
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
}

fn load_from_str(s: &str, global: &mut GlobalEnv) {
    let predef_exprs = crate::parse_all(s).expect("Parse error at predef.lisp");
    for predef_expr in predef_exprs {
        crate::eval(&predef_expr, global).expect("Eval error at predef.lisp");
    }
}
