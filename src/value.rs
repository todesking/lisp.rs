use crate::eval::Ast;
use crate::eval::EvalError;
use crate::eval::Result;
use crate::local_env::LocalEnv;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i32),
    Sym(Rc<str>),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
    Ref(Rc<RefValue>),
}

// TODO: enum ValueRef { Box, Rc }

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RefValue {
    Lambda {
        param_names: Vec<Rc<str>>,
        rest_name: Option<Rc<str>>,
        bodies: Rc<[Ast]>,
        expr: Rc<Ast>,
        env: Option<Rc<RefCell<LocalEnv>>>,
    },
    Fun {
        name: String,
        fun: Fun,
    },
}

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct Fun(pub Rc<dyn for<'a> Fn(&'a [Value]) -> Result>);

impl PartialEq for Fun {
    fn eq(&self, rhs: &Self) -> bool {
        let pl = self.0.as_ref() as *const _ as *const ();
        let pr = rhs.0.as_ref() as *const _ as *const ();
        pl == pr
    }
}
impl Eq for Fun {}
impl std::fmt::Debug for Fun {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("<primitive function>")
    }
}

impl Value {
    pub fn int(n: i32) -> Value {
        Value::Int(n)
    }
    pub fn bool(v: bool) -> Value {
        Value::Bool(v)
    }
    pub fn nil() -> Value {
        Value::Nil
    }
    pub fn cons<T1: Into<Value>, T2: Into<Value>>(car: T1, cdr: T2) -> Value {
        Value::Cons(Rc::new(car.into()), Rc::new(cdr.into()))
    }
    pub fn sym(name: &str) -> Value {
        Value::Sym(Rc::from(name))
    }
    pub fn fun<F>(name: &str, f: F) -> Value
    where
        F: for<'a> Fn(&'a [Value]) -> Result + 'static,
    {
        Value::Ref(Rc::new(RefValue::Fun {
            name: name.to_string(),
            fun: Fun(Rc::new(f)),
        }))
    }
    pub fn ref_value(v: RefValue) -> Value {
        Value::Ref(Rc::new(v))
    }
    pub fn is_nil(&self) -> bool {
        self == &Value::Nil
    }
    pub fn is_cyclic_reference_safe(&self) -> bool {
        match self {
            Value::Cons(..) => false,
            Value::Ref(..) => false,
            _ => true,
        }
    }
    pub fn as_sym(&self) -> Option<&Rc<str>> {
        match self {
            Value::Sym(name) => Some(name),
            _ => None,
        }
    }
    pub fn to_vec(&self) -> Option<Vec<&Value>> {
        let (values, tail) = self.to_improper_vec();
        if tail.is_nil() {
            Some(values)
        } else {
            None
        }
    }
    pub fn to_improper_vec(&self) -> (Vec<&Value>, &Value) {
        let mut rest = self;
        let mut values = Vec::new();
        while let Value::Cons(car, cdr) = rest {
            rest = cdr.as_ref();
            values.push(car.as_ref());
        }
        (values, rest)
    }
    pub fn collect_improper<'a, F, T, E>(
        &'a self,
        f: F,
    ) -> std::result::Result<(Vec<T>, Option<T>), E>
    where
        F: Fn(&'a Value) -> std::result::Result<T, E>,
        T: 'a,
    {
        if self == &Value::Nil {
            return Ok((vec![], None));
        }

        let mut rest = self;
        let mut values = Vec::new();
        while let Value::Cons(car, cdr) = rest {
            rest = cdr;
            let v = f(car)?;
            values.push(v);
        }
        match rest {
            Value::Nil => Ok((values, None)),
            x => {
                let v = f(x)?;
                Ok((values, Some(v)))
            }
        }
    }
    // TODO: Use macro to abstract funX functions
    pub fn fun0<F, R>(name: &str, f: F) -> Value
    where
        F: Fn() -> R + 'static,
        R: Into<Value>,
    {
        let fun = move |args: &[Value]| {
            if !args.is_empty() {
                Err(EvalError::ArgumentSize)
            } else {
                let v = f();
                Ok(v.into())
            }
        };
        Value::fun(name, fun)
    }
    pub fn fun1<F, T1, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1) -> R + 'static,
        T1: Extract,
        R: Into<Value>,
    {
        let fun = move |args: &[Value]| {
            if args.len() != 1 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(&args[0]).ok_or(EvalError::InvalidArg)?;
            let v = f(x1).into();
            Ok(v)
        };
        Value::fun(name, fun)
    }
    pub fn fun2<F, T1, T2, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T2) -> R + 'static,
        T1: Extract,
        T2: Extract,
        R: Into<Value>,
    {
        let fun = move |args: &[Value]| {
            if args.len() != 2 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(&args[0]).ok_or(EvalError::InvalidArg)?;
            let x2 = T2::extract(&args[1]).ok_or(EvalError::InvalidArg)?;
            let v = f(x1, x2).into();
            Ok(v)
        };
        Value::fun(name, fun)
    }
    pub fn fun_fold<F, T1>(name: &str, init: T1, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let fun = move |args: &[Value]| {
            let mut a = init.clone();
            for x in args.iter() {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(a.into())
        };
        Value::fun(name, fun)
    }
    pub fn fun_reduce<F, T1>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let fun = move |args: &[Value]| {
            let mut it = args.iter();
            let a = it.next().ok_or(EvalError::ArgumentSize)?;
            let mut a = T1::extract(a).ok_or(EvalError::InvalidArg)?;
            for x in it {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(a.into())
        };
        Value::fun(name, fun)
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Value::Int(v) => fmt.write_fmt(format_args!("{}", v)),
            Value::Bool(v) => fmt.write_fmt(format_args!("{}", v)),
            Value::Sym(v) => fmt.write_str(v.as_ref()),
            Value::Cons(..) | Value::Nil => {
                fmt.write_str("(")?;
                let (heads, tail) = self.to_improper_vec();
                if let Some((last, heads)) = heads.split_last() {
                    for x in heads {
                        fmt.write_fmt(format_args!("{}", x))?;
                        fmt.write_str(" ")?;
                    }
                    fmt.write_fmt(format_args!("{}", last))?;
                    if !tail.is_nil() {
                        fmt.write_str(" . ")?;
                        fmt.write_fmt(format_args!("{}", tail))?;
                    }
                }
                fmt.write_str(")")?;
                Ok(())
            }
            Value::Ref(r) => fmt.write_fmt(format_args!("{}", r)),
        }
    }
}

impl std::fmt::Display for RefValue {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            RefValue::Lambda {
                param_names,
                rest_name,
                ..
            } => {
                fmt.write_str("#<lambda")?;
                if let Some((last_param, param_names)) = param_names.split_last() {
                    fmt.write_str(" ")?;
                    for p in param_names {
                        fmt.write_str(p)?;
                        fmt.write_str(" ")?;
                    }
                    fmt.write_str(last_param)?;
                }
                for r in rest_name {
                    fmt.write_str(" . ")?;
                    fmt.write_str(r)?;
                }
                fmt.write_str(">")
            }
            RefValue::Fun { name, .. } => {
                fmt.write_str("#<primitive:")?;
                fmt.write_str(name)?;
                fmt.write_str(">")
            }
        }
    }
}

pub trait ToValue {
    fn to_value(self) -> Value;
}

impl<T: ToValue> From<T> for Value {
    fn from(x: T) -> Value {
        x.to_value()
    }
}

impl ToValue for &i32 {
    fn to_value(self) -> Value {
        Value::Int(*self)
    }
}

impl ToValue for i32 {
    fn to_value(self) -> Value {
        Value::Int(self)
    }
}

impl ToValue for bool {
    fn to_value(self) -> Value {
        Value::Bool(self)
    }
}

pub trait Extract
where
    Self: Sized,
{
    fn extract(x: &Value) -> Option<Self>;
}

impl Extract for i32 {
    fn extract(x: &Value) -> Option<Self> {
        match x {
            Value::Int(n) => Some(*n),
            _ => None,
        }
    }
}

impl Extract for bool {
    fn extract(x: &Value) -> Option<Self> {
        match x {
            Value::Bool(v) => Some(*v),
            _ => None,
        }
    }
}

#[macro_export]
macro_rules! list {
    () =>  { Value::Nil };
    ($x: expr) => { Value::cons(Value::from($x), Value::Nil) };
    ($x: expr ; $y: expr) => { Value::cons(Value::from($x), Value::from($y)) };
    ($x: expr, $($xs: expr),+$(; $y: expr)?) => { Value::cons(Value::from($x), list!($($xs),+$(; $y)?)) };
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_display() {
        assert_eq!(Value::int(42).to_string(), "42");
        assert_eq!(Value::bool(true).to_string(), "true");
        assert_eq!(Value::sym("foo").to_string(), "foo");
        assert_eq!(Value::nil().to_string(), "()");
        assert_eq!(list![1, 2, 3].to_string(), "(1 2 3)");
        assert_eq!(Value::cons(1, Value::cons(2, 3)).to_string(), "(1 2 . 3)");
        assert_eq!(list![list![1, 2], 3].to_string(), "((1 2) 3)");
        assert_eq!(
            Value::ref_value(RefValue::Lambda {
                param_names: vec![Rc::from("x")],
                rest_name: Some(Rc::from("rest")),
                bodies: Vec::<Ast>::new().into_iter().collect::<Rc<[Ast]>>(),
                expr: Rc::new(Ast::Const(Value::nil())),
                env: None
            })
            .to_string(),
            "#<lambda x . rest>"
        );
        assert_eq!(
            Value::fun("f", |_| Ok(Value::nil())).to_string(),
            "#<primitive:f>"
        );
    }

    #[test]
    fn test_list_macro() {
        assert_eq!(list!(), Value::Nil);
        assert_eq!(list!(1), Value::cons(Value::Int(1), Value::Nil));
        assert_eq!(
            list!(Value::Int(1), 2),
            Value::cons(Value::Int(1), Value::cons(Value::Int(2), Value::Nil))
        );
        assert_eq!(list!(1; 2), Value::cons(Value::int(1), Value::int(2)));
        assert_eq!(
            list!(1, 2; 3),
            Value::cons(Value::int(1), Value::cons(Value::int(2), Value::int(3)))
        );
    }
}
