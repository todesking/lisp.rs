use crate::name::AbsName;
use crate::name::MemberName;
use crate::name::SimpleName;
use crate::EvalError;
use crate::Value;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Debug, Default)]
pub struct GlobalEnv {
    ids: HashMap<MemberName, usize>,
    values: Vec<Value>,
    macros: HashMap<MemberName, Value>,
    imports: HashMap<SimpleName, MemberName>,
    module_members: HashMap<AbsName, HashSet<SimpleName>>,
}

pub struct ReadOnly<'a>(&'a GlobalEnv);

pub trait GlobalWrite<'a>: AsRef<GlobalEnv> {
    fn set_by_id(&mut self, _id: usize, _value: Value) -> Option<()> {
        None
    }
    fn set(&mut self, _key: MemberName, _value: Value) -> Option<()> {
        None
    }
    fn set_macro(&mut self, _key: MemberName, _value: Value) -> Option<()> {
        None
    }
    fn define_module_member(&mut self, _mname: AbsName, _name: SimpleName) -> Option<()> {
        Some(())
    }
    fn import(&mut self, _name: SimpleName, _full_name: MemberName) -> Option<()> {
        Some(())
    }
}

impl<'a> AsRef<GlobalEnv> for ReadOnly<'a> {
    fn as_ref(&self) -> &GlobalEnv {
        self.0
    }
}
impl<'a> GlobalWrite<'a> for ReadOnly<'a> {}
impl AsRef<GlobalEnv> for GlobalEnv {
    fn as_ref(&self) -> &GlobalEnv {
        self
    }
}
impl<'a> GlobalWrite<'a> for GlobalEnv {
    fn set_by_id(&mut self, id: usize, value: Value) -> Option<()> {
        GlobalEnv::set_by_id(self, id, value);
        Some(())
    }
    fn set(&mut self, key: MemberName, value: Value) -> Option<()> {
        GlobalEnv::set(self, key, value);
        Some(())
    }
    fn set_macro(&mut self, key: MemberName, value: Value) -> Option<()> {
        GlobalEnv::set_macro(self, key, value);
        Some(())
    }
    fn define_module_member(&mut self, mname: AbsName, name: SimpleName) -> Option<()> {
        self.module_members
            .entry(mname)
            .or_insert_with(HashSet::new)
            .insert(name);
        Some(())
    }
    fn import(&mut self, name: SimpleName, absname: MemberName) -> Option<()> {
        self.imports.insert(name, absname);
        Some(())
    }
}

impl GlobalEnv {
    pub fn new() -> GlobalEnv {
        Default::default()
    }
    pub fn read_only(&self) -> ReadOnly {
        ReadOnly(self)
    }
    pub fn lookup_global_id(&self, name: &MemberName) -> Option<usize> {
        self.ids.get(name).copied()
    }
    pub fn lookup(&self, key: &MemberName) -> Option<&Value> {
        self.lookup_global_id(key).map(|i| &self.values[i])
    }
    pub fn lookup_macro(&self, key: &MemberName) -> Option<&Value> {
        self.macros.get(key)
    }
    pub fn next_id(&self) -> usize {
        self.values.len()
    }
    pub fn imports(&self) -> &HashMap<SimpleName, MemberName> {
        &self.imports
    }
    pub fn module_members(&self) -> &HashMap<AbsName, HashSet<SimpleName>> {
        &self.module_members
    }

    pub fn get(&self, id: usize) -> &Value {
        &self.values[id]
    }
    pub fn set_by_id(&mut self, id: usize, value: Value) {
        self.values[id] = value;
    }
    pub fn set(&mut self, key: MemberName, value: Value) {
        if let Some(id) = self.lookup_global_id(&key) {
            self.values[id] = value;
        } else {
            self.values.push(value);
            self.ids.insert(key, self.values.len() - 1);
        }
    }
    pub fn set_macro(&mut self, key: MemberName, value: Value) {
        self.macros.insert(key, value);
    }
    pub fn set_fun<F>(&mut self, name: MemberName, f: F)
    where
        F: Fn(&[Value]) -> Result<Value, EvalError> + 'static,
    {
        let value = Value::fun(&name.to_string(), f);
        self.set(name, value);
    }
    pub fn set_fun1<F>(&mut self, name: MemberName, f: F)
    where
        F: Fn(&Value) -> Result<Value, EvalError> + 'static,
    {
        self.set_fun(name, move |args| {
            if args.len() != 1 {
                Err(EvalError::IllegalArgument(Value::list(args.iter())))
            } else {
                f(&args[0])
            }
        })
    }
    pub fn set_fun2<F>(&mut self, name: MemberName, f: F)
    where
        F: Fn(&Value, &Value) -> Result<Value, EvalError> + 'static,
    {
        self.set_fun(name, move |args| {
            if args.len() != 2 {
                Err(EvalError::IllegalArgument(Value::list(args.iter())))
            } else {
                f(&args[0], &args[1])
            }
        })
    }
    pub fn set_global_fun<F>(&mut self, name: MemberName, f: F)
    where
        F: Fn(&[Value], &GlobalEnv) -> Result<Value, EvalError> + 'static,
    {
        let value = Value::global_fun(&name.to_string(), f);
        self.set(name, value);
    }
    pub fn ls(&self) -> impl Iterator<Item = &MemberName> {
        self.ids.keys()
    }
    pub fn ls_macro(&self) -> impl Iterator<Item = &MemberName> {
        self.macros.keys()
    }
}
