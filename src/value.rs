use crate::eval::EvalError;
use crate::eval::Result;
use crate::local_env::LocalEnv;
use std::rc::Rc;

// TODO: Regroup to SExpr { Value(SValue), Ref(Rc<SRef>) }
// SValue { Int(i32), ... }
// SRef { Cons(SExpr, Sexpr), Lambda(...), ... }
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i32),
    Sym(String),
    Nil,
    Cons(Rc<Value>, Rc<Value>),
    Lambda(
        Vec<String>,
        Option<String>,
        Vec<Rc<Value>>,
        Option<Rc<LocalEnv>>,
    ),
    Fun(FunData),
    Bool(bool),
}

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub struct FunData {
    pub name: String,
    pub fun: Rc<dyn for<'a> Fn(&'a [Rc<Value>]) -> Result>,
}

impl PartialEq for FunData {
    fn eq(&self, rhs: &Self) -> bool {
        let pl = self.fun.as_ref() as *const _ as *const ();
        let pr = rhs.fun.as_ref() as *const _ as *const ();
        self.name == rhs.name && pl == pr
    }
}
impl Eq for FunData {}
impl std::fmt::Debug for FunData {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.debug_struct("")
            .field("name", &self.name)
            .field("fun", &"<function>")
            .finish()
    }
}

impl Value {
    pub fn cons<T1: Into<Value>, T2: Into<Value>>(car: T1, cdr: T2) -> Value {
        Value::Cons(Rc::new(car.into()), Rc::new(cdr.into()))
    }
    pub fn sym<S: Into<String>>(name: S) -> Value {
        Value::Sym(name.into())
    }
    pub fn to_vec(&self) -> Option<Vec<Rc<Value>>> {
        // TODO: refactor to use collect_improper()
        if self == &Value::Nil {
            return Some(vec![]);
        }

        let mut rest = self;
        let mut values = Vec::new();
        while let Value::Cons(car, cdr) = rest {
            rest = cdr;
            values.push(car.clone());
        }
        match rest {
            Value::Nil => Some(values),
            _ => None,
        }
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
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            if !args.is_empty() {
                Err(EvalError::ArgumentSize)
            } else {
                let v = f();
                Ok(Rc::new(v.into()))
            }
        });
        Value::Fun(FunData { name, fun })
    }
    pub fn fun1<F, T1, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1) -> R + 'static,
        T1: Extract,
        R: Into<Value>,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            if args.len() != 1 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(args[0].as_ref()).ok_or(EvalError::InvalidArg)?;
            let v = f(x1).into();
            Ok(Rc::new(v))
        });
        Value::Fun(FunData { name, fun })
    }
    pub fn fun2<F, T1, T2, R>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T2) -> R + 'static,
        T1: Extract,
        T2: Extract,
        R: Into<Value>,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            if args.len() != 2 {
                return Err(EvalError::ArgumentSize);
            }
            let x1 = T1::extract(args[0].as_ref()).ok_or(EvalError::InvalidArg)?;
            let x2 = T2::extract(args[1].as_ref()).ok_or(EvalError::InvalidArg)?;
            let v = f(x1, x2).into();
            Ok(Rc::new(v))
        });
        Value::Fun(FunData { name, fun })
    }
    pub fn fun_fold<F, T1>(name: &str, init: T1, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            let mut a = init.clone();
            for x in args.iter() {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(Rc::new(a.into()))
        });
        Value::Fun(FunData { name, fun })
    }
    pub fn fun_reduce<F, T1>(name: &str, f: F) -> Value
    where
        F: Fn(T1, T1) -> T1 + 'static,
        T1: Extract + Clone + Into<Value> + 'static,
    {
        let name = name.to_string();
        let fun = Rc::new(move |args: &[Rc<Value>]| {
            let mut it = args.iter();
            let a = it.next().ok_or(EvalError::ArgumentSize)?;
            let a = T1::extract(a).ok_or(EvalError::InvalidArg)?;
            let mut a = a;
            for x in it {
                match T1::extract(x) {
                    Some(x) => a = f(a, x),
                    None => return Err(EvalError::InvalidArg),
                }
            }
            Ok(Rc::new(a.into()))
        });
        Value::Fun(FunData { name, fun })
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

impl<'a, T> ToValue for &'a Vec<T>
where
    &'a T: Into<Value>,
{
    fn to_value(self) -> Value {
        self.iter().rev().fold(Value::Nil, |a, x| Value::cons(x, a))
    }
}

impl<'a> ToValue for &'a Vec<Rc<Value>> {
    fn to_value(self) -> Value {
        self.iter()
            .rev()
            .fold(Value::Nil, |a, x| Value::Cons(x.clone(), Rc::new(a)))
    }
}

impl ToValue for &[Rc<Value>] {
    fn to_value(self) -> Value {
        self.iter()
            .rev()
            .fold(Value::Nil, |a, x| Value::Cons(x.clone(), Rc::new(a)))
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

#[macro_export]
macro_rules! list {
    () =>  { Value::Nil };
    ($x: expr) => { Value::cons(Value::from($x), Value::Nil) };
    ($x: expr, $($xs: expr),+) => { Value::cons(Value::from($x), list!($($xs),+)) };
}
