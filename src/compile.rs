use crate::ast::Ast;
use crate::ast::MatchPattern;
use crate::ast::QuasiQuote;
use crate::ast::VarRef;
use crate::name::AbsName;
use crate::name::Name;
use crate::name::SimpleName;
use crate::static_env::StaticEnv;
use crate::value::LambdaDef;
use crate::value::RefValue;
use crate::EvalError;
use crate::GlobalEnv;
use crate::TopAst;
use crate::Value;

use std::rc::Rc;

fn illegal_argument_error<T>(value: Value) -> Result<T, EvalError> {
    Err(EvalError::IllegalArgument(value))
}

fn expand_macro(expr: &Value, env: &StaticEnv) -> Result<Value, EvalError> {
    let mut expr = expr.clone();
    loop {
        match extract_macro_call(&expr, env) {
            None => return Ok(expr),
            Some((macro_body, macro_args)) => {
                let macro_args = macro_args.to_vec().ok_or_else(|| {
                    EvalError::Macro(Box::new(EvalError::IllegalArgument(macro_args)))
                })?;
                expr = crate::eval::eval_macro(&macro_body, macro_args, env.global())?;
            }
        }
    }
}

fn extract_macro_call(expr: &Value, env: &StaticEnv) -> Option<(Value, Value)> {
    let (car, cdr) = expr.to_cons()?;
    let name = car.as_sym()?;
    let name = env.resolve_global_name(name)?;
    let macro_def = env.global().lookup_macro(&name)?;
    Some((macro_def.clone(), cdr))
}

pub fn build_top_ast(expr: &Value, global: &GlobalEnv) -> Result<TopAst, EvalError> {
    let mut env = StaticEnv::new(global);
    build_top_ast_impl(expr, &mut env)
}
pub fn build_top_ast_within_module(
    expr: &Value,
    global: &GlobalEnv,
    current_module: Option<AbsName>,
) -> Result<TopAst, EvalError> {
    let mut env = StaticEnv::new_with_current_module(global, current_module);
    build_top_ast_impl(expr, &mut env)
}
fn build_top_ast_impl(expr: &Value, env: &mut StaticEnv) -> Result<TopAst, EvalError> {
    let expr = match expand_macro(expr, env) {
        Ok(expr) => expr,
        Err(err) => return Ok(TopAst::Expr(Ast::Error(err))),
    };
    if let Some((car, cdr)) = expr.to_cons() {
        match car.as_sym().map(|r| &**r) {
            Some("begin") => {
                // top-level begin
                let values = cdr
                    .to_vec()
                    .ok_or_else(|| EvalError::IllegalArgument(cdr.clone()))?;
                if let Some((head, rest)) = values.split_first() {
                    let mut exprs = vec![];
                    let head = build_top_ast_impl(head, env)?;
                    exprs.push(head);
                    for v in rest {
                        exprs.push(TopAst::Delay(env.current_module().clone(), v.clone()));
                    }
                    Ok(TopAst::Begin(exprs))
                } else {
                    Ok(TopAst::Expr(Ast::Const(Value::Nil)))
                }
            }
            Some(deftype @ "__define") | Some(deftype @ "__defmacro") => {
                if let Some((name, value)) = cdr.to_list2() {
                    let name = name
                        .to_simple_name()
                        .ok_or_else(|| EvalError::IllegalArgument(cdr.clone()))?;
                    let current_module =
                        env.current_module().clone().unwrap_or_else(AbsName::global);
                    let member_name = current_module.member_name(name);
                    env.new_global(member_name.clone());
                    let value = build_ast(&value, &env)?;
                    let ast = match deftype {
                        "__define" => TopAst::Define(member_name, value),
                        "__defmacro" => TopAst::DefMacro(member_name, value),
                        _ => unreachable!(),
                    };
                    Ok(ast)
                } else {
                    illegal_argument_error(cdr)
                }
            }
            Some("module") => {
                let err = || EvalError::IllegalArgument(cdr.clone());
                let (name, body) = cdr.to_cons().ok_or_else(err)?;
                let current_module = env.current_module().clone().unwrap_or_else(AbsName::root);
                let name = name.to_simple_name().ok_or_else(err)?;
                let body = list!["begin"; body];
                env.new_module_member(current_module.clone(), name.clone());
                let the_module = current_module.into_child_name(name);
                let body =
                    env.module_scope(the_module.clone(), |env| build_top_ast_impl(&body, env))?;
                Ok(TopAst::Begin(vec![TopAst::DefModule(the_module), body]))
            }
            Some("import-from") => {
                let err = || EvalError::IllegalArgument(cdr.clone());
                let (mod_name, names) = cdr.to_cons().ok_or_else(err)?;
                let mod_name = mod_name.as_sym().ok_or_else(err)?;
                let names = names.to_vec().ok_or_else(err)?;
                // TODO: use as_simple_name()
                let names = names
                    .iter()
                    .map(|n| n.as_sym())
                    .collect::<Option<Vec<_>>>()
                    .ok_or_else(err)?;
                let names = names
                    .into_iter()
                    .map(|n| SimpleName::parse(&**n))
                    .collect::<Option<Vec<_>>>()
                    .ok_or_else(err)?;
                let current_module = env.current_module().clone().unwrap_or_else(AbsName::root);
                let mod_name = env
                    .module_scope(current_module, |env| env.resolve_global_name(mod_name))
                    .map(|n| n.into_abs_name())
                    .ok_or_else(err)?;
                if !env.has_module(&mod_name) {
                    return Err(EvalError::ModuleNotFound(mod_name.to_string()));
                }
                let undefined_names = names
                    .iter()
                    .filter(|&name| !env.has_module_member(mod_name.clone(), name.clone()))
                    .collect::<Vec<_>>();
                if !undefined_names.is_empty() {
                    let undefined_names = undefined_names
                        .into_iter()
                        .map(|n| Value::sym(n.as_ref()))
                        .collect::<Vec<_>>();
                    return Err(EvalError::IllegalArgument(Value::list(
                        undefined_names.iter(),
                    )));
                }
                for name in names.iter() {
                    env.new_import(name.clone(), mod_name.member_name(name.clone()));
                }
                let imports = names
                    .into_iter()
                    .map(|name| {
                        let child_name = mod_name.member_name(name.clone());
                        TopAst::Import(name, child_name)
                    })
                    .collect::<Vec<_>>();
                Ok(TopAst::Begin(imports))
            }
            _ => {
                let ast = build_ast(&expr, env)?;
                Ok(TopAst::Expr(ast))
            }
        }
    } else {
        let ast = build_ast(&expr, env)?;
        Ok(TopAst::Expr(ast))
    }
}

fn build_ast(expr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    let expr = match expand_macro(expr, env) {
        Ok(expr) => expr,
        Err(err) => return Ok(Ast::Error(err)),
    };
    let expr = &expr;
    match expr {
        Value::Int(..) | Value::Bool(..) | Value::Nil | Value::Str(..) => {
            Ok(Ast::Const(expr.clone()))
        }
        Value::Sym(name) => {
            let name = name.as_ref().to_owned();
            match env.lookup(&name) {
                Some(VarRef::Global(id)) => Ok(Ast::GetGlobal(name, id)),
                Some(VarRef::Local(depth, index)) => Ok(Ast::GetLocal(name, depth, index)),
                Some(VarRef::Rec(depth, index)) => Ok(Ast::GetRec(name, depth, index)),
                Some(VarRef::Argument(index)) => Ok(Ast::GetArgument(name, index)),
                None => Ok(Ast::Error(EvalError::VariableNotFound(name.to_string()))),
            }
        }
        Value::Ref(r) => match &**r {
            RefValue::Cons(car, cdr) => build_ast_from_cons(&car.borrow(), &cdr.borrow(), env),
            RefValue::RecLambda { .. }
            | RefValue::Lambda { .. }
            | RefValue::Fun { .. }
            | RefValue::GlobalFun { .. } => Ok(Ast::Const(expr.clone())),
        },
    }
}

fn build_ast_from_cons(car: &Value, cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    match car {
        Value::Sym(name) if &**name == "quote" => build_ast_quote(cdr),
        Value::Sym(name) if &**name == "__define" => Err(EvalError::DefineInLocalContext),
        Value::Sym(name) if &**name == "if" => build_ast_if(cdr, env),
        Value::Sym(name) if &**name == "lambda" => build_ast_lambda(cdr, env),
        Value::Sym(name) if &**name == "begin" =>
        // expr-level begin
        {
            build_ast(&list![list!["lambda", list![]; cdr.clone()]], env)
        }
        Value::Sym(name) if &**name == "set-local!" => build_ast_set_local(cdr, true, env),
        Value::Sym(name) if &**name == "unsafe-set-local!" => build_ast_set_local(cdr, false, env),
        Value::Sym(name) if &**name == "set-global!" => {
            build_ast_set_global(cdr, env).or_else(|err| Ok(Ast::Error(err)))
        }
        Value::Sym(name) if &**name == "catch-error" => build_ast_catch_error(cdr, env),
        Value::Sym(name) if &**name == "letrec" => build_ast_letrec(cdr, env),
        Value::Sym(name) if &**name == "quasiquote" => build_ast_quasiquote(cdr, env),
        Value::Sym(name) if &**name == "unquote" => Ok(Ast::Error(EvalError::QuasiQuote)),
        Value::Sym(name) if &**name == "unquote-splicing" => Ok(Ast::Error(EvalError::QuasiQuote)),
        Value::Sym(name) if &**name == "if-match" => build_ast_if_match(cdr, env),
        f => build_ast_apply(f, cdr, env),
    }
}

fn build_ast_quote(cdr: &Value) -> Result<Ast, EvalError> {
    if let Some(x) = cdr.to_list1() {
        Ok(Ast::Const(x))
    } else {
        illegal_argument_error(cdr.clone())
    }
}

fn build_ast_if(cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    if let Some((cond, th, el)) = cdr.to_list3() {
        let cond = build_ast(&cond, env)?;
        let th = build_ast(&th, env)?;
        let el = build_ast(&el, env)?;
        Ok(Ast::If(Box::new(cond), Box::new(th), Box::new(el)))
    } else {
        illegal_argument_error(cdr.clone())
    }
}

fn build_ast_lambda(cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    match cdr.to_vec().as_deref() {
        Some([params, bodies @ .., expr]) => {
            let (param_names, rest_name) = params.collect_improper(|v| match v {
                Value::Sym(name) => {
                    let name = SimpleName::parse(&**name)
                        .ok_or_else(|| EvalError::IllegalArgument(cdr.clone()))?;
                    Ok(name)
                }
                _ => Err(EvalError::SymbolRequired),
            })?;
            let body_env = env.extended(param_names.clone(), rest_name.clone());
            let bodies = bodies
                .iter()
                .map(|v| build_ast(v, &body_env))
                .collect::<Result<Rc<[Ast]>, EvalError>>()?;
            let expr = Rc::new(build_ast(expr, &body_env)?);
            let depth = body_env.local_depth();
            Ok(Ast::Lambda {
                param_names,
                rest_name,
                bodies,
                expr,
                depth,
            })
        }
        _ => Err(EvalError::IllegalArgument(cdr.clone())),
    }
}

fn build_ast_catch_error(cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    if let Some((handler, expr)) = cdr.to_list2() {
        let handler = build_ast(&handler, env).map(Box::new)?;
        let expr = build_ast(&expr, env).map(Box::new)?;
        Ok(Ast::CatchError { handler, expr })
    } else {
        illegal_argument_error(cdr.clone())
    }
}

fn build_ast_letrec(cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    let err = || EvalError::IllegalArgument(cdr.clone());
    let (defs, body) = cdr.to_cons().ok_or_else(err)?;
    let defs = defs.to_vec().ok_or_else(err)?;
    let (env, defs) = extract_rec_lambda_defs(&defs, env, err)?;
    let body = body.to_vec().ok_or_else(err)?;
    let mut body = body
        .iter()
        .map(|b| build_ast(b, &env))
        .collect::<Result<Vec<Ast>, EvalError>>()?;
    let expr = body.pop().ok_or_else(err)?;
    let expr = Box::new(expr);
    let defs = defs.into_iter().map(|d| d.1).collect();
    let rec_depth = env.rec_depth();
    let local_depth = env.local_depth();
    Ok(Ast::LetRec {
        defs,
        body,
        expr,
        rec_depth,
        local_depth,
    })
}

fn build_ast_quasiquote(cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    let value = cdr.to_list1().ok_or(EvalError::QuasiQuote)?;
    let qq =
        build_quasiquote(&value, None, env).unwrap_or_else(|err| QuasiQuote::expr(Ast::Error(err)));
    Ok(Ast::QuasiQuote(qq))
}

fn build_ast_if_match(cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    let (expr, th, el) = cdr
        .to_list3()
        .ok_or_else(|| EvalError::IllegalArgument(cdr.clone()))?;
    let (pat, th) = th
        .to_list2()
        .ok_or_else(|| EvalError::IllegalArgument(th.clone()))?;
    let expr = build_ast(&expr, env)?;
    let mut capture_names = Vec::new();
    let pat = build_pattern(&pat, &mut capture_names)?;
    let capture_size = capture_names.len();
    let th_env = env.extended(capture_names.clone(), None);
    let th = build_ast(&th, &th_env)?;
    let th = Ast::Lambda {
        param_names: capture_names,
        rest_name: None,
        bodies: Rc::from(vec![]),
        expr: Rc::new(th),
        depth: th_env.local_depth(),
    };
    let el = build_ast(&el, env)?;
    Ok(Ast::IfMatch(
        capture_size,
        Box::new(expr),
        pat,
        Box::new(th),
        Box::new(el),
    ))
}

fn build_ast_apply(f: &Value, cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    match cdr.to_vec() {
        None => illegal_argument_error(cdr.clone()),
        Some(args) => {
            let f = build_ast(f, env)?;
            let mut arg_values = Vec::with_capacity(args.len());
            for arg in args.iter() {
                let arg = build_ast(arg, env)?;
                arg_values.push(arg);
            }
            Ok(Ast::Apply(Box::new(f), arg_values))
        }
    }
}

fn build_pattern(pat: &Value, env: &mut Vec<SimpleName>) -> Result<MatchPattern, EvalError> {
    match pat {
        Value::Sym(name) => {
            // TODO: more informative error(make EvalError::SimpleNameRequired)
            let name = SimpleName::parse(&**name).ok_or(EvalError::SymbolRequired)?;
            if name.as_ref() == "_" {
                Ok(MatchPattern::Any)
            } else if let Some(index) = env.iter().position(|n| n == &name) {
                Ok(MatchPattern::SameAs(name, index))
            } else {
                let index = env.len();
                env.push(name.to_owned());
                Ok(MatchPattern::Capture(name, index))
            }
        }
        Value::Int(..) | Value::Bool(..) | Value::Nil | Value::Str(..) => {
            Ok(MatchPattern::Const(pat.clone()))
        }
        Value::Ref(r) => match &**r {
            RefValue::Cons(car, cdr) => {
                let car = car.borrow();
                let cdr = cdr.borrow();
                match &*car {
                    Value::Sym(name) if &**name == "quote" => {
                        let value = cdr
                            .to_list1()
                            .ok_or_else(|| EvalError::IllegalArgument(pat.clone()))?;
                        Ok(MatchPattern::Const(value))
                    }
                    _ => {
                        let car = build_pattern(&car, env)?;
                        let cdr = build_pattern(&cdr, env)?;
                        Ok(MatchPattern::Cons(car.into(), cdr.into()))
                    }
                }
            }
            _ => Err(EvalError::IllegalArgument(pat.clone())),
        },
    }
}

fn build_quasiquote(
    car: &Value,
    cdr: Option<&Value>,
    env: &StaticEnv,
) -> Result<QuasiQuote, EvalError> {
    if let Some((caar, cdar)) = car.to_cons() {
        match caar {
            Value::Sym(name) if &*name == "quasiquote" => Err(EvalError::QuasiQuote),
            Value::Sym(name) if &*name == "unquote" => {
                let arg = cdar.to_list1().ok_or(EvalError::QuasiQuote)?;
                let ast = build_ast(&arg, env)?;
                if let Some(cdr) = cdr {
                    let cdr = build_quasiquote(cdr, None, env)?;
                    Ok(QuasiQuote::cons(QuasiQuote::expr(ast), cdr))
                } else {
                    Ok(QuasiQuote::expr(ast))
                }
            }
            Value::Sym(name) if &*name == "unquote-splicing" => {
                let arg = cdar.to_list1().ok_or(EvalError::QuasiQuote)?;
                let arg = build_ast(&arg, env)?;
                let cdr = cdr.ok_or(EvalError::QuasiQuote)?;
                let cdr = build_quasiquote(cdr, None, env)?;
                Ok(QuasiQuote::append(arg, cdr))
            }
            caar => {
                let car = build_quasiquote(&caar, Some(&cdar), env)?;
                if let Some(cdr) = cdr {
                    let cdr = build_quasiquote(cdr, None, env)?;
                    Ok(QuasiQuote::cons(car, cdr))
                } else {
                    Ok(car)
                }
            }
        }
    } else {
        match car {
            Value::Sym(name) if &**name == "quasiquote" => Err(EvalError::QuasiQuote),
            _ => {
                let car = QuasiQuote::Const(car.clone());
                if let Some(cdr) = cdr {
                    let cdr = build_quasiquote(cdr, None, env)?;
                    Ok(QuasiQuote::cons(car, cdr))
                } else {
                    Ok(car)
                }
            }
        }
    }
}

#[allow(clippy::type_complexity)]
fn extract_rec_lambda_defs<'a, 'b, E: Fn() -> EvalError + Copy>(
    raw: impl IntoIterator<Item = &'a Value>,
    env: &'b StaticEnv,
    err: E,
) -> Result<(StaticEnv<'b>, Vec<(SimpleName, LambdaDef)>), EvalError> {
    let defs = raw
        .into_iter()
        .map(|raw| extract_raw_lambda_def(raw).ok_or_else(err))
        .collect::<Result<Vec<_>, _>>()?;
    let env = env.rec_extended(defs.iter().map(|(name, ..)| name.clone()));
    let defs = defs
        .into_iter()
        .map(|(name, param_names, rest_name, bodies, expr)| {
            let env = env.extended(param_names.clone(), rest_name.clone());
            let bodies = bodies
                .into_iter()
                .map(|b| build_ast(&b, &env))
                .collect::<Result<Vec<_>, _>>()?;
            let bodies = Rc::from(bodies);
            let expr = build_ast(&expr, &env)?;
            let expr = Rc::new(expr);
            Ok((
                name,
                LambdaDef {
                    param_names,
                    rest_name,
                    bodies,
                    expr,
                },
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((env, defs))
}

/// returns `(name, param_names, rest_name, bodies, expr)`
#[allow(clippy::type_complexity)]
fn extract_raw_lambda_def(
    raw: &Value,
) -> Option<(
    SimpleName,
    Vec<SimpleName>,
    Option<SimpleName>,
    Vec<Value>,
    Value,
)> {
    let (names, bodies) = raw.to_cons()?;
    let (name, param_names, rest_name) = extract_lambda_names(&names)?;
    let mut bodies = bodies.to_vec()?;
    let expr = bodies.pop()?;
    Some((name, param_names, rest_name, bodies, expr))
}

#[allow(clippy::type_complexity)]
fn extract_lambda_names(expr: &Value) -> Option<(SimpleName, Vec<SimpleName>, Option<SimpleName>)> {
    let (name, params) = expr.to_cons()?;
    let name = name.to_simple_name()?;
    let (param_names, rest_name) = params.to_improper_vec();
    let param_names = param_names
        .iter()
        .map(|pn| pn.to_simple_name())
        .collect::<Option<Vec<_>>>()?;
    let rest_name = if rest_name == Value::nil() {
        None
    } else {
        Some(rest_name.to_simple_name()?)
    };
    Some((name, param_names, rest_name))
}

fn build_ast_set_local(expr: &Value, safe: bool, env: &StaticEnv) -> Result<Ast, EvalError> {
    if let Some((name, value)) = expr.to_list2() {
        let name = name.as_sym().ok_or(EvalError::SymbolRequired)?;
        let name = name.to_string();
        let value = build_ast(&value, env)?;
        let value = Box::new(value);
        let value = if safe {
            Box::new(Ast::EnsureSafe(value))
        } else {
            value
        };
        if let Some(var) = env.lookup(&name) {
            match var {
                VarRef::Global(..) => Ok(Ast::Error(EvalError::VariableNotFound(name))),
                VarRef::Local(depth, index) => Ok(Ast::SetLocal {
                    name,
                    depth,
                    index,
                    value,
                }),
                VarRef::Rec(..) => Ok(Ast::Error(EvalError::ReadOnly(name))),
                VarRef::Argument(index) => Ok(Ast::SetArg { name, index, value }),
            }
        } else {
            Ok(Ast::Error(EvalError::VariableNotFound(name)))
        }
    } else {
        illegal_argument_error(expr.clone())
    }
}

fn build_ast_set_global(expr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    if let Some((name, value)) = expr.to_list2() {
        let name = name.as_sym().ok_or(EvalError::SymbolRequired)?;
        let name =
            Name::parse(name).ok_or_else(|| EvalError::VariableNotFound(name.to_string()))?;
        let name = match name {
            Name::Single(name) => {
                let current_module = env.current_module().clone().unwrap_or_else(AbsName::global);
                current_module.into_member_name(name)
            }
            Name::Absolute(full_name) => full_name,
            Name::Relative(_, name) => {
                return Err(EvalError::VariableNotFound(name.to_string()));
            }
        };
        let err = || EvalError::VariableNotFound(name.to_string());
        let id = env.lookup_global_id(&name).ok_or_else(err)?;
        let value = build_ast(&value, env)?;
        let value = Box::new(value);
        Ok(Ast::SetGlobal {
            name: name.to_string(),
            id,
            value,
        })
    } else {
        illegal_argument_error(expr.clone())
    }
}
