use crate::build_top_ast;
use crate::eval;
use crate::value::Extract;
use crate::EvalError;
use crate::GlobalEnv;
use crate::Value;
use std::rc::Rc;

pub fn load_predef(global: &mut GlobalEnv) {
    let ns_global = crate::name::AbsName::global();

    global.set_fun2(ns_global.member_name_or_die("eq?"), |lhs, rhs| {
        Ok(Value::bool(lhs == rhs))
    });

    global.set_fun(ns_global.member_name_or_die("error"), |args| {
        Err(EvalError::User(Value::list(args.iter())))
    });

    global.set_fun(ns_global.member_name_or_die("make-symbol"), |args| {
        if args.len() != 1 {
            return Err(EvalError::illegal_argument(args));
        }
        if let Some(s) = args[0].as_str() {
            Ok(Value::Sym(s.clone()))
        } else {
            Err(EvalError::illegal_argument(args))
        }
    });

    global.set_fun1(ns_global.member_name_or_die("to-string"), |v| {
        let content = match v {
            Value::Sym(v) | Value::Str(v) => v.clone(),
            Value::Int(v) => Rc::from(v.to_string()),
            Value::Bool(v) => Rc::from(v.to_string()),
            _ => return Err(EvalError::illegal_argument(&[v.clone()])),
        };
        Ok(Value::Str(content))
    });
    global.set_fun(ns_global.member_name_or_die("str-+"), |args| {
        let args = args
            .iter()
            .map(|v| match v {
                Value::Str(v) => Ok(v.as_ref()),
                _ => Err(EvalError::illegal_argument(args)),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Value::Str(Rc::from(args.join(""))))
    });

    global.set_global_fun(
        ns_global.member_name_or_die("macro-expand"),
        |args, global| {
            if args.len() != 1 {
                Err(EvalError::illegal_argument(args))
            } else {
                build_top_ast(&args[0], global).map(|ast| ast.to_value())
            }
        },
    );

    global.set_global_fun(ns_global.member_name_or_die("print-global"), |_, global| {
        dbg!(&global); // (print-global)
        Ok(Value::Nil)
    });

    load_arithmetic(global);
    load_list_ops(global);
    load_from_str(include_str!("predef.lisp"), global).expect("error in predef.lisp")
}

fn load_arithmetic(global: &mut GlobalEnv) {
    let ns_global = crate::name::AbsName::global();
    global.set(
        ns_global.member_name_or_die("+"),
        Value::fun_reduce("+", |l: i32, r: i32| l + r),
    );
    global.set_fun(ns_global.member_name_or_die("-"), |args| {
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
    global.set(
        ns_global.member_name_or_die("*"),
        Value::fun_reduce("*", |l: i32, r: i32| l * r),
    );
    global.set(
        ns_global.member_name_or_die("/"),
        Value::fun2("/", |l: i32, r: i32| l / r),
    );
    global.set(
        ns_global.member_name_or_die("%"),
        Value::fun2("%", |l: i32, r: i32| l % r),
    );
    global.set(
        ns_global.member_name_or_die("<"),
        Value::fun2("<", |l: i32, r: i32| l < r),
    );
    global.set(
        ns_global.member_name_or_die("<="),
        Value::fun2("<=", |l: i32, r: i32| l <= r),
    );
    global.set(
        ns_global.member_name_or_die(">"),
        Value::fun2(">", |l: i32, r: i32| l > r),
    );
    global.set(
        ns_global.member_name_or_die(">="),
        Value::fun2(">=", |l: i32, r: i32| l >= r),
    );
}

fn load_list_ops(global: &mut GlobalEnv) {
    let ns_global = crate::name::AbsName::global();

    global.set_fun2(ns_global.member_name_or_die("set-car!"), |x, v| {
        x.set_car(v.clone(), true)
    });
    global.set_fun2(ns_global.member_name_or_die("set-cdr!"), |x, v| {
        x.set_cdr(v.clone(), true)
    });
    global.set_fun2(ns_global.member_name_or_die("unsafe-set-car!"), |x, v| {
        x.set_car(v.clone(), false)
    });
    global.set_fun2(ns_global.member_name_or_die("unsafe-set-cdr!"), |x, v| {
        x.set_cdr(v.clone(), false)
    });
}

fn load_from_str(s: &str, global: &mut GlobalEnv) -> Result<(), (Value, EvalError)> {
    let predef_exprs = crate::parse_all(s).expect("Parse error at predef.lisp");
    for predef_expr in predef_exprs {
        eval(&predef_expr, global).map_err(|err| (predef_expr.clone(), err))?;
    }
    Ok(())
}
