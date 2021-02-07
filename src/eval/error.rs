use crate::value::Value;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EvalError {
    VariableNotFound(String),
    IllegalArgument(Value),
    SymbolRequired,
    InvalidArg,
    CantApply(Value, Box<[Value]>),
    Unsafe,
    User(Value),
    DefineInLocalContext,
}

impl EvalError {
    pub fn illegal_argument(args: &[Value]) -> EvalError {
        EvalError::IllegalArgument(Value::list(args.iter()))
    }
    pub fn to_tuple(&self) -> (&'static str, Value) {
        match self {
            EvalError::VariableNotFound(name) => {
                ("VariableNotFound", list![Value::sym(name.as_ref())])
            }
            EvalError::IllegalArgument(value) => ("IllegalArgument", value.clone()),
            EvalError::SymbolRequired => ("SymbolRequired", Value::nil()),
            EvalError::InvalidArg => ("InvalidArg", Value::nil()),
            EvalError::CantApply(f, args) => {
                ("CantApply", list![f.clone(); Value::list(args.iter())])
            }
            EvalError::Unsafe => ("Unsafe", Value::nil()),
            EvalError::User(value) => ("User", value.clone()),
            EvalError::DefineInLocalContext => ("DefineInLocalContext", Value::nil()),
        }
    }
}

impl std::fmt::Display for EvalError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let (err, data) = self.to_tuple();
        fmt.write_str(err)?;
        fmt.write_str("[")?;
        fmt.write_fmt(format_args!("{}", data))?;
        fmt.write_str("]")
    }
}
impl std::error::Error for EvalError {}
