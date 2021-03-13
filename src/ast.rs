use crate::value::LambdaDef;
use crate::EvalError;
use crate::Value;

use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopAst {
    /// (module abs-name, short name, ast)
    Define(String, String, Ast),
    DefMacro(String, Ast),
    /// (abs parent module name, simple module name)
    DefModule(String, String),
    /// (simple name, abs name)
    Import(String, String),
    Expr(Ast),
    Begin(Vec<TopAst>),
    Delay(Option<ModName>, Value),
}
impl TopAst {
    // Note: this is for debugging purporse only.
    // Consistency(i.e. ast == build_top_ast(ast.to_value())) not guaranteed.
    pub fn to_value(&self) -> Value {
        match self {
            TopAst::Begin(asts) => {
                let asts = asts.iter().map(|x| x.to_value()).collect::<Vec<_>>();
                list!["begin"; Value::list(asts.iter())]
            }
            TopAst::Define(module_name, name, ast) => {
                let mut abs_name = module_name.to_string();
                abs_name.push(':');
                abs_name.push_str(name);
                list!["__define", &abs_name, ast.to_value()]
            }
            TopAst::DefMacro(name, ast) => {
                list!["__defmacro", name, ast.to_value()]
            }
            TopAst::DefModule(mname, name) => {
                list!["define-module", mname, name]
            }
            TopAst::Import(name, absname) => list!["import-name", name, absname],
            TopAst::Expr(ast) => ast.to_value(),
            TopAst::Delay(mname, value) => list![
                "<delay>",
                &mname
                    .as_ref()
                    .map(|n| n.to_string())
                    .unwrap_or_else(|| "(global)".into()),
                value.clone()
            ],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModName {
    Root,
    Child(Box<ModName>, String),
}
impl ModName {
    pub fn make(parts: &[&str]) -> ModName {
        ModName::Root.make_relative(parts)
    }
    pub fn make_relative(self, parts: &[&str]) -> ModName {
        parts
            .iter()
            .fold(self, |a, x| ModName::Child(a.into(), x.to_string()))
    }
    pub fn global() -> ModName {
        Self::make(&["global"])
    }
    pub fn abs_name(&self, name: &str) -> String {
        let mut buf = String::new();
        self.to_string_impl(&mut buf);
        buf.push(':');
        buf.push_str(name);
        buf
    }
    fn to_string_impl(&self, buf: &mut String) {
        match self {
            ModName::Root => {}
            ModName::Child(parent, name) => {
                parent.to_string_impl(buf);
                buf.push(':');
                buf.push_str(name);
            }
        }
    }
    pub fn as_child(&self) -> Option<(&ModName, &String)> {
        match self {
            ModName::Root => None,
            ModName::Child(parent, name) => Some((parent, name)),
        }
    }
    pub fn child_module(&self, name: &str) -> ModName {
        ModName::Child(self.clone().into(), name.to_string())
    }
}
impl std::fmt::Display for ModName {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        let mut buf = String::new();
        self.to_string_impl(&mut buf);
        fmt.write_str(&buf)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ast {
    Const(Value),
    GetGlobal(String, usize),
    GetLocal(String, usize, usize),
    GetArgument(String, usize),
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
    GetRec(String, usize, usize),
    LetRec {
        rec_depth: usize,
        local_depth: usize,
        defs: Vec<LambdaDef>,
        body: Vec<Ast>,
        expr: Box<Ast>,
    },
    QuasiQuote(QuasiQuote),
    IfMatch(usize, Box<Ast>, MatchPattern, Box<Ast>, Box<Ast>),
}

fn lambda_to_value(
    param_names: &[Rc<str>],
    rest_name: &Option<Rc<str>>,
    bodies: &[Ast],
    expr: &Ast,
) -> Value {
    let rest_name = rest_name
        .clone()
        .map(|n| Value::sym(&*n))
        .unwrap_or(Value::Nil);
    let params = param_names
        .iter()
        .map(|n| Value::sym(n))
        .rev()
        .fold(rest_name, |a, x| Value::cons(x, a));
    let body = bodies
        .iter()
        .rev()
        .fold(list![expr.to_value()], |a, x| Value::cons(x.to_value(), a));
    list![params; body]
}
impl Ast {
    fn to_value(&self) -> Value {
        match self {
            Ast::Const(v) => match v {
                Value::Bool(..) | Value::Int(..) | Value::Str(..) | Value::Nil => v.clone(),
                _ => list!["quote", v.clone()],
            },
            Ast::GetGlobal(name, ..)
            | Ast::GetLocal(name, ..)
            | Ast::GetArgument(name, ..)
            | Ast::GetRec(name, ..) => Value::sym(name),
            Ast::If(cond, th, el) => list![
                Value::sym("if"),
                cond.to_value(),
                th.to_value(),
                el.to_value()
            ],
            Ast::Lambda {
                param_names,
                rest_name,
                bodies,
                expr,
                ..
            } => {
                list!["lambda"; lambda_to_value(param_names, rest_name, bodies, expr)]
            }
            Ast::Apply(f, xs) => {
                let xs = Value::list(xs.iter().map(|x| x.to_value()).collect::<Vec<_>>().iter());
                list![f.to_value(); xs]
            }
            Ast::SetLocal { name, value, .. }
            | Ast::SetArg { name, value, .. }
            | Ast::SetGlobal { name, value, .. } => list![
                Value::sym("unsafe-set-local!"),
                Value::sym(name),
                value.to_value()
            ],
            Ast::EnsureSafe(value) => list!["ensure-safe", value.to_value()],
            Ast::CatchError { handler, expr } => list![
                Value::sym("catch-error"),
                handler.to_value(),
                expr.to_value()
            ],
            Ast::Error(err) => {
                let (err, payload) = err.to_tuple();
                list!["error", err, payload]
            }
            Ast::LetRec {
                defs, body, expr, ..
            } => {
                let defs = defs
                    .iter()
                    .map(|def| {
                        lambda_to_value(&def.param_names, &def.rest_name, &def.bodies, &def.expr)
                    })
                    .collect::<Vec<_>>();
                let body = body
                    .iter()
                    .map(|x| x.to_value())
                    .rev()
                    .fold(expr.to_value(), |a, x| Value::cons(x, a));
                list!["letrec", Value::list(defs.iter()); body]
            }
            Ast::QuasiQuote(qq) => list!["quasiquote", qq.to_value()],
            Ast::IfMatch(_, expr, pat, th, el) => list![
                "if-match",
                expr.to_value(),
                list![pat.to_value(), th.to_value()],
                el.to_value()
            ],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchPattern {
    Const(Value),
    Capture(String, usize),
    Cons(Box<MatchPattern>, Box<MatchPattern>),
    SameAs(String, usize),
    Any,
}
impl MatchPattern {
    pub fn match_and_bind(&self, value: &Value, out: &mut Vec<Value>) -> bool {
        match self {
            MatchPattern::Any => true,
            MatchPattern::Const(v) => v == value,
            MatchPattern::Capture(_, index) => {
                assert!(out.len() == *index);
                out.push(value.clone());
                true
            }
            MatchPattern::SameAs(_, index) => &out[*index] == value,
            MatchPattern::Cons(pcar, pcdr) => {
                if let Some((vcar, vcdr)) = value.to_cons() {
                    pcar.match_and_bind(&vcar, out) && pcdr.match_and_bind(&vcdr, out)
                } else {
                    false
                }
            }
        }
    }
    fn to_value(&self) -> Value {
        match self {
            MatchPattern::Any => Value::sym("_"),
            MatchPattern::Const(v) => Ast::Const(v.clone()).to_value(),
            MatchPattern::Capture(name, _) => Value::sym(name),
            MatchPattern::SameAs(name, _) => Value::sym(name),
            MatchPattern::Cons(car, cdr) => list![car.to_value(); cdr.to_value()],
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum QuasiQuote {
    Const(Value),
    Cons(Box<QuasiQuote>, Box<QuasiQuote>),
    Expr(Box<Ast>),
    Append(Box<Ast>, Box<QuasiQuote>),
}
impl QuasiQuote {
    pub fn cons(car: QuasiQuote, cdr: QuasiQuote) -> QuasiQuote {
        QuasiQuote::Cons(car.into(), cdr.into())
    }
    pub fn append(expr: Ast, l: QuasiQuote) -> QuasiQuote {
        QuasiQuote::Append(expr.into(), l.into())
    }
    pub fn expr(ast: Ast) -> QuasiQuote {
        QuasiQuote::Expr(ast.into())
    }
    fn to_value(&self) -> Value {
        match self {
            QuasiQuote::Const(v) => v.clone(),
            QuasiQuote::Cons(car, cdr) => Value::cons(car.to_value(), cdr.to_value()),
            QuasiQuote::Expr(ast) => list!["unquote", ast.to_value()],
            QuasiQuote::Append(expr, list) => {
                list![list!["unquote-splicing", expr.to_value()]; list.to_value()]
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum VarRef {
    Global(usize),
    Local(usize, usize),
    Rec(usize, usize),
    Argument(usize),
}
