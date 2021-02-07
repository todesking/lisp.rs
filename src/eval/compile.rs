use crate::eval::EvalError;
use crate::eval::GlobalEnv;
use crate::value::RefValue;
use crate::value::Value;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TopAst {
    Define(String, Ast),
    Expr(Ast),
}

#[derive(Clone, Debug, PartialEq, Eq)]
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
}

pub enum VarRef {
    Local(usize, usize),
    Global(usize),
    Argument(usize),
}

#[derive(Clone)]
struct StaticEnv<'a> {
    global: &'a GlobalEnv,
    current_global: Option<(String, usize, bool)>,
    local: std::collections::HashMap<String, (usize, usize)>,
    local_depth: usize,
    args: std::collections::HashMap<String, usize>,
}
impl<'a> StaticEnv<'a> {
    fn new(global: &GlobalEnv) -> StaticEnv {
        StaticEnv {
            global,
            current_global: None,
            local: Default::default(),
            local_depth: 0,
            args: Default::default(),
        }
    }
    fn new_with_current<'b>(global: &'a GlobalEnv, name: &'b str) -> StaticEnv<'a> {
        StaticEnv {
            global,
            current_global: Some((name.to_owned(), global.next_id(), false)),
            local: Default::default(),
            local_depth: 0,
            args: Default::default(),
        }
    }
    fn lookup(&self, name: &str) -> Option<VarRef> {
        if let Some(index) = self.args.get(name) {
            Some(VarRef::Argument(*index))
        } else if let Some((depth, index)) = self.local.get(name) {
            Some(VarRef::Local(*depth, *index))
        } else {
            self.current_global
                .as_ref()
                .filter(|(gname, _, initialized)| gname == name && *initialized)
                .map(|(_, id, _)| VarRef::Global(*id))
                .or_else(|| self.global.lookup_global_id(name).map(VarRef::Global))
        }
    }
    fn lookup_global_id(&self, name: &str) -> Option<usize> {
        self.global.lookup_global_id(name)
    }
    fn extended<'b>(&self, names: impl Iterator<Item = &'b str>) -> StaticEnv<'a> {
        let mut env = StaticEnv {
            global: self.global,
            current_global: self
                .current_global
                .clone()
                .map(|(name, id, _)| (name, id, true)),
            local: self.local.clone(),
            local_depth: self.local_depth + 1,
            args: Default::default(),
        };
        for (name, i) in self.args.iter() {
            env.local.insert(name.clone(), (env.local_depth, *i));
        }
        for (i, name) in names.enumerate() {
            env.args.insert(name.to_string(), i);
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
            Some(VarRef::Local(depth, index)) => Ok(Ast::GetLocal(depth, index)),
            Some(VarRef::Global(id)) => Ok(Ast::GetGlobal(id)),
            Some(VarRef::Argument(index)) => Ok(Ast::GetArgument(index)),
            None => Ok(Ast::Error(EvalError::VariableNotFound(name.to_string()))),
        },
        Value::Ref(r) => match r.as_ref() {
            RefValue::Cons(car, cdr) => build_ast_from_cons(&car.borrow(), &cdr.borrow(), env),
            RefValue::Lambda { .. } => unimplemented!(),
            RefValue::Fun { .. } => unimplemented!(),
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
                let body_env = env.extended(
                    param_names
                        .iter()
                        .chain(rest_name.iter())
                        .map(|v| v.as_ref()),
                );
                let bodies = bodies
                    .iter()
                    .map(|v| build_ast(v, &body_env))
                    .collect::<Result<Rc<[Ast]>, EvalError>>()?;
                let expr = Rc::new(build_ast(expr, &body_env)?);
                Ok(Ast::Lambda {
                    param_names,
                    rest_name,
                    bodies,
                    expr,
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
