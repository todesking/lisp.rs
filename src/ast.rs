use crate::value::LambdaDef;
use crate::EvalError;
use crate::Value;

use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopAst {
    Define(AbsName, Ast),
    DefMacro(AbsName, Ast),
    DefModule(AbsName),
    Import(SimpleName, AbsName),
    Expr(Ast),
    Begin(Vec<TopAst>),
    Delay(Option<AbsName>, Value),
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
            TopAst::Define(name, ast) => {
                list!["__define", &name.to_string(), ast.to_value()]
            }
            TopAst::DefMacro(name, ast) => {
                list!["__defmacro", &name.to_string(), ast.to_value()]
            }
            TopAst::DefModule(name) => {
                list!["define-module", &name.to_string()]
            }
            TopAst::Import(name, absname) => {
                list!["import-name", name.as_ref(), &absname.to_string()]
            }
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbsName(Vec<SimpleName>);
impl AbsName {
    pub fn new(parts: impl Into<Vec<SimpleName>>) -> AbsName {
        AbsName(parts.into())
    }
    pub fn global() -> AbsName {
        AbsName(vec![SimpleName::from("global").unwrap()])
    }
    pub fn root() -> AbsName {
        AbsName(vec![])
    }

    // TODO: Make name: SimpleName
    pub fn child_name(&self, name: &SimpleName) -> AbsName {
        let mut abs_name = self.clone();
        abs_name.0.push(name.clone());
        abs_name
    }

    pub fn child_name_or_die(&self, name: &str) -> AbsName {
        let name = SimpleName::from(name).unwrap();
        self.child_name(&name)
    }

    pub fn relative_name(&self, names: impl IntoIterator<Item = SimpleName>) -> AbsName {
        let mut v = self.0.clone();
        for name in names {
            v.push(name);
        }
        AbsName(v)
    }

    // TODO: remove this
    pub fn split(&self) -> (AbsName, SimpleName) {
        let last = self.0.last().unwrap().clone();
        let mut heads = self.0.clone();
        heads.pop();
        (AbsName(heads), last)
    }
}
impl std::fmt::Display for AbsName {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        use std::fmt::Write;
        for part in &self.0 {
            fmt.write_char(':')?;
            part.fmt(fmt)?;
        }
        Ok(())
    }
}

// TODO: Use Rc<str>
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SimpleName(String);
impl SimpleName {
    pub fn from<S: Into<String> + AsRef<str>>(s: S) -> Option<SimpleName> {
        if s.as_ref().chars().any(|c| c == ':') {
            None
        } else {
            Some(SimpleName(s.into()))
        }
    }
}
impl AsRef<str> for SimpleName {
    fn as_ref(&self) -> &str {
        &self.0
    }
}
impl std::fmt::Display for SimpleName {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str(&self.0)?;
        Ok(())
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
    Capture(SimpleName, usize),
    Cons(Box<MatchPattern>, Box<MatchPattern>),
    SameAs(SimpleName, usize),
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
            MatchPattern::Capture(name, _) => Value::sym(name.as_ref()),
            MatchPattern::SameAs(name, _) => Value::sym(name.as_ref()),
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
