use crate::eval::EvalError;
use crate::eval::GlobalEnv;
use crate::value::LambdaDef;
use crate::value::RefValue;
use crate::value::Value;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopAst {
    Define(String, Ast),
    Expr(Ast),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Const(Value),
    GetGlobal(usize),
    GetLocal(usize, usize),
    GetArgument(usize),
    If(Box<Ast>, Box<Ast>, Box<Ast>),
    Lambda {
        param_names: Vec<Rc<str>>,
        rest_name: Option<Rc<str>>,
        bodies: Rc<[Ast]>,
        expr: Rc<Ast>,
        depth: usize,
    },
    Apply(Box<Ast>, Vec<Ast>),
    SetLocal {
        name: String,
        depth: usize,
        index: usize,
        value: Box<Ast>,
    },
    SetArg {
        name: String,
        index: usize,
        value: Box<Ast>,
    },
    SetGlobal {
        name: String,
        id: usize,
        value: Box<Ast>,
    },
    EnsureSafe(Box<Ast>),
    CatchError {
        handler: Box<Ast>,
        expr: Box<Ast>,
    },
    Error(EvalError),
    GetRec(usize, usize),
    LetRec {
        rec_depth: usize,
        defs: Vec<LambdaDef>,
        body: Vec<Ast>,
        expr: Box<Ast>,
    },
    QuasiQuote(QuasiQuote),
    IfMatch(usize, Box<Ast>, MatchPattern, Box<Ast>, Box<Ast>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchPattern {
    Const(Value),
    Capture(usize),
    Cons(Box<MatchPattern>, Box<MatchPattern>),
    SameAs(usize),
    Any,
}
impl MatchPattern {
    pub fn match_and_bind(&self, value: &Value, out: &mut Vec<Value>) -> bool {
        match self {
            MatchPattern::Any => true,
            MatchPattern::Const(v) => v == value,
            MatchPattern::Capture(index) => {
                assert!(out.len() == *index);
                out.push(value.clone());
                true
            }
            MatchPattern::SameAs(index) => &out[*index] == value,
            MatchPattern::Cons(pcar, pcdr) => {
                if let Some((vcar, vcdr)) = value.to_cons() {
                    pcar.match_and_bind(&vcar, out) && pcdr.match_and_bind(&vcdr, out)
                } else {
                    false
                }
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum QuasiQuote {
    Const(Value),
    Cons(Box<QuasiQuote>, Box<QuasiQuote>),
    Expr(Box<Ast>),
    Append(Box<QuasiQuote>, Box<QuasiQuote>),
}
impl QuasiQuote {
    fn cons(car: QuasiQuote, cdr: QuasiQuote) -> QuasiQuote {
        QuasiQuote::Cons(car.into(), cdr.into())
    }
    fn append(l1: QuasiQuote, l2: QuasiQuote) -> QuasiQuote {
        QuasiQuote::Append(l1.into(), l2.into())
    }
    fn expr(ast: Ast) -> QuasiQuote {
        QuasiQuote::Expr(ast.into())
    }
}

#[derive(Clone)]
pub enum VarRef {
    Global(usize),
    Local(usize, usize),
    Rec(usize, usize),
    Argument(usize),
}

#[derive(Clone)]
struct StaticEnv<'a> {
    global: &'a GlobalEnv,
    current_global: Option<(String, usize)>,
    locals: std::collections::HashMap<String, VarRef>,
    local_depth: usize,
    args: Vec<String>,
    rec_depth: usize,
}
impl<'a> StaticEnv<'a> {
    fn new(global: &GlobalEnv) -> StaticEnv {
        StaticEnv {
            global,
            current_global: None,
            locals: Default::default(),
            local_depth: 0,
            args: Default::default(),
            rec_depth: 0,
        }
    }
    fn new_with_current<'b>(global: &'a GlobalEnv, name: &'b str) -> StaticEnv<'a> {
        StaticEnv {
            global,
            current_global: Some((name.to_owned(), global.next_id())),
            locals: Default::default(),
            local_depth: 0,
            args: Default::default(),
            rec_depth: 0,
        }
    }
    fn lookup(&self, name: &str) -> Option<VarRef> {
        if let Some(var_ref) = self.locals.get(name) {
            Some(var_ref.clone())
        } else {
            self.current_global
                .as_ref()
                .filter(|(gname, _)| gname == name)
                .map(|(_, id)| VarRef::Global(*id))
                .or_else(|| self.global.lookup_global_id(name).map(VarRef::Global))
        }
    }
    fn lookup_global_id(&self, name: &str) -> Option<usize> {
        self.global.lookup_global_id(name)
    }
    fn extended(&self, names: &[Rc<str>], rest_name: &Option<Rc<str>>) -> StaticEnv<'a> {
        let mut env = StaticEnv {
            global: self.global,
            current_global: self.current_global.clone(),
            locals: self.locals.clone(),
            local_depth: self.local_depth + 1,
            args: Default::default(),
            rec_depth: self.rec_depth,
        };
        for (i, name) in self.args.iter().enumerate() {
            env.locals
                .insert(name.clone(), VarRef::Local(env.local_depth, i));
        }
        for (i, name) in names.iter().chain(rest_name.iter()).enumerate() {
            env.args.push(name.to_string());
            env.locals.insert(name.to_string(), VarRef::Argument(i));
        }
        env
    }
    fn rec_extended<'b>(&self, names: impl Iterator<Item = &'b str>) -> StaticEnv<'a> {
        let mut env = self.clone();
        env.rec_depth += 1;
        for (i, name) in names.enumerate() {
            env.locals
                .insert(name.to_string(), VarRef::Rec(env.rec_depth, i));
        }
        env
    }
}

fn illegal_argument_error<T>(value: Value) -> Result<T, EvalError> {
    Err(EvalError::IllegalArgument(value))
}

pub fn build_top_ast(expr: &Value, global: &GlobalEnv) -> Result<TopAst, EvalError> {
    if let Some((car, cdr)) = expr.to_cons() {
        if let Some("define") = car.as_sym().map(|r| r.as_ref()) {
            if let Some((name, value)) = cdr.to_list2() {
                match name {
                    Value::Sym(name) => {
                        let env = StaticEnv::new_with_current(global, &*name);
                        let value = build_ast(&value, &env)?;
                        Ok(TopAst::Define(name.to_string(), value))
                    }
                    _ => Err(EvalError::SymbolRequired),
                }
            } else {
                illegal_argument_error(cdr)
            }
        } else {
            let ast = build_ast(expr, &StaticEnv::new(global))?;
            Ok(TopAst::Expr(ast))
        }
    } else {
        let ast = build_ast(expr, &StaticEnv::new(global))?;
        Ok(TopAst::Expr(ast))
    }
}
fn build_ast(expr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    match expr {
        Value::Int(..) | Value::Bool(..) | Value::Nil => Ok(Ast::Const(expr.clone())),
        Value::Sym(name) => match env.lookup(name) {
            Some(VarRef::Global(id)) => Ok(Ast::GetGlobal(id)),
            Some(VarRef::Local(depth, index)) => Ok(Ast::GetLocal(depth, index)),
            Some(VarRef::Rec(depth, index)) => Ok(Ast::GetRec(depth, index)),
            Some(VarRef::Argument(index)) => Ok(Ast::GetArgument(index)),
            None => Ok(Ast::Error(EvalError::VariableNotFound(name.to_string()))),
        },
        Value::Ref(r) => match r.as_ref() {
            RefValue::Cons(car, cdr) => build_ast_from_cons(&car.borrow(), &cdr.borrow(), env),
            RefValue::RecLambda { .. } | RefValue::Lambda { .. } | RefValue::Fun { .. } => {
                Ok(Ast::Const(expr.clone()))
            }
        },
    }
}

fn build_ast_from_cons(car: &Value, cdr: &Value, env: &StaticEnv) -> Result<Ast, EvalError> {
    match car {
        Value::Sym(name) if name.as_ref() == "quote" => {
            if let Some(x) = cdr.to_list1() {
                Ok(Ast::Const(x))
            } else {
                illegal_argument_error(cdr.clone())
            }
        }
        Value::Sym(name) if name.as_ref() == "define" => Err(EvalError::DefineInLocalContext),
        Value::Sym(name) if name.as_ref() == "if" => {
            if let Some((cond, th, el)) = cdr.to_list3() {
                let cond = build_ast(&cond, env)?;
                let th = build_ast(&th, env)?;
                let el = build_ast(&el, env)?;
                Ok(Ast::If(Box::new(cond), Box::new(th), Box::new(el)))
            } else {
                illegal_argument_error(cdr.clone())
            }
        }
        Value::Sym(name) if name.as_ref() == "lambda" => match cdr.to_vec().as_deref() {
            Some([params, bodies @ .., expr]) => {
                let (param_names, rest_name) = params.collect_improper(|v| match v {
                    Value::Sym(name) => Ok(name.clone()),
                    _ => Err(EvalError::SymbolRequired),
                })?;
                let body_env = env.extended(&param_names, &rest_name);
                let bodies = bodies
                    .iter()
                    .map(|v| build_ast(v, &body_env))
                    .collect::<Result<Rc<[Ast]>, EvalError>>()?;
                let expr = Rc::new(build_ast(expr, &body_env)?);
                let depth = body_env.local_depth;
                Ok(Ast::Lambda {
                    param_names,
                    rest_name,
                    bodies,
                    expr,
                    depth,
                })
            }
            _ => Err(EvalError::IllegalArgument(cdr.clone())),
        },
        Value::Sym(name) if name.as_ref() == "set-local!" => build_ast_set_local(cdr, true, env),
        Value::Sym(name) if name.as_ref() == "unsafe-set-local!" => {
            build_ast_set_local(cdr, false, env)
        }
        Value::Sym(name) if name.as_ref() == "set-global!" => build_ast_set_global(cdr, env),
        Value::Sym(name) if name.as_ref() == "catch-error" => {
            if let Some((handler, expr)) = cdr.to_list2() {
                let handler = build_ast(&handler, env).map(Box::new)?;
                let expr = build_ast(&expr, env).map(Box::new)?;
                Ok(Ast::CatchError { handler, expr })
            } else {
                illegal_argument_error(cdr.clone())
            }
        }
        Value::Sym(name) if name.as_ref() == "letrec" => {
            let err = || EvalError::IllegalArgument(cdr.clone());
            let (defs, body) = cdr.to_cons().ok_or_else(err)?;
            let defs = defs.to_vec().ok_or_else(err)?;
            let (env, defs) = extract_lambda_defs(&defs, env, err)?;
            let body = body.to_vec().ok_or_else(err)?;
            let body: Vec<Ast> = body
                .iter()
                .map(|b| build_ast(b, &env))
                .collect::<Result<Vec<Ast>, EvalError>>()?;
            let (expr, body) = body.split_last().ok_or_else(err)?;
            let body = body.to_vec();
            let expr = Box::new(expr.clone());
            let defs = defs.into_iter().map(|d| d.1).collect();
            let rec_depth = env.rec_depth;
            Ok(Ast::LetRec {
                defs,
                body,
                expr,
                rec_depth,
            })
        }
        Value::Sym(name) if name.as_ref() == "quasiquote" => {
            let value = cdr.to_list1().ok_or(EvalError::QuasiQuote)?;
            let qq = build_quasiquote(&value, None, env)
                .unwrap_or_else(|err| QuasiQuote::expr(Ast::Error(err)));
            Ok(Ast::QuasiQuote(qq))
        }
        Value::Sym(name) if name.as_ref() == "unquote" => Ok(Ast::Error(EvalError::QuasiQuote)),
        Value::Sym(name) if name.as_ref() == "unquote-splicing" => {
            Ok(Ast::Error(EvalError::QuasiQuote))
        }
        Value::Sym(name) if &**name == "if-match" => {
            let (expr, th, el) = cdr
                .to_list3()
                .ok_or_else(|| EvalError::IllegalArgument(cdr.clone()))?;
            let (pat, th) = th
                .to_list2()
                .ok_or_else(|| EvalError::IllegalArgument(th.clone()))?;
            let expr = build_ast(&expr, env)?;
            let mut pat_env = Vec::new();
            let pat = build_pattern(&pat, &mut pat_env)?;
            let pat_env = pat_env
                .iter()
                .map(|n| Rc::from(n.clone()))
                .collect::<Vec<_>>();
            let capture_size = pat_env.len();
            let th_env = env.extended(&pat_env, &None);
            let th = build_ast(&th, &th_env)?;
            let th = Ast::Lambda {
                param_names: pat_env,
                rest_name: None,
                bodies: Rc::from(vec![]),
                expr: Rc::new(th),
                depth: env.local_depth,
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
        f => match cdr.to_vec() {
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
        },
    }
}

fn build_pattern(pat: &Value, env: &mut Vec<String>) -> Result<MatchPattern, EvalError> {
    match pat {
        Value::Sym(name) => {
            let name = name.as_ref();
            if name == "_" {
                Ok(MatchPattern::Any)
            } else if let Some(index) = env.iter().position(|n| n == name) {
                Ok(MatchPattern::SameAs(index))
            } else {
                let index = env.len();
                env.push(name.to_owned());
                Ok(MatchPattern::Capture(index))
            }
        }
        Value::Int(..) | Value::Bool(..) | Value::Nil => Ok(MatchPattern::Const(pat.clone())),
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
                let arg = QuasiQuote::Expr(Box::new(arg));
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
fn extract_lambda_defs<'a, 'b, E: Fn() -> EvalError + Copy>(
    raw: impl IntoIterator<Item = &'a Value>,
    env: &'b StaticEnv,
    err: E,
) -> Result<(StaticEnv<'b>, Vec<(Rc<str>, LambdaDef)>), EvalError> {
    let defs = raw
        .into_iter()
        .map(|raw| extract_raw_lambda_def(raw).ok_or_else(err))
        .collect::<Result<Vec<_>, _>>()?;
    let env = env.rec_extended(defs.iter().map(|(name, ..)| name.as_ref()));
    let defs = defs
        .into_iter()
        .map(|(name, param_names, rest_name, bodies, expr)| {
            let env = env.extended(&param_names, &rest_name);
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

#[allow(clippy::type_complexity)]
fn extract_raw_lambda_def(
    raw: &Value,
) -> Option<(Rc<str>, Vec<Rc<str>>, Option<Rc<str>>, Vec<Value>, Value)> {
    let (names, bodies) = raw.to_cons()?;
    let (name, param_names, rest_name) = extract_lambda_names(&names)?;
    let bodies = bodies.to_vec()?;
    let (expr, bodies) = bodies.split_last()?;
    Some((name, param_names, rest_name, bodies.to_vec(), expr.clone()))
}

#[allow(clippy::type_complexity)]
fn extract_lambda_names(expr: &Value) -> Option<(Rc<str>, Vec<Rc<str>>, Option<Rc<str>>)> {
    let (name, params) = expr.to_cons()?;
    let name = name.as_sym().cloned()?;
    let (param_names, rest_name) = params.to_improper_vec();
    let param_names = param_names
        .iter()
        .map(|pn| pn.as_sym().cloned())
        .collect::<Option<Vec<_>>>()?;
    let rest_name = if rest_name == Value::nil() {
        None
    } else {
        Some(rest_name.as_sym().cloned()?)
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
        let name = name.as_ref().to_owned();
        let id = env
            .lookup_global_id(&name)
            .ok_or_else(|| EvalError::VariableNotFound(name.clone()))?;
        let value = build_ast(&value, env)?;
        let value = Box::new(value);
        Ok(Ast::SetGlobal { name, id, value })
    } else {
        illegal_argument_error(expr.clone())
    }
}
