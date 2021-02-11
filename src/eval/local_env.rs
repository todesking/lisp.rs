use crate::value::LambdaDef;
use crate::value::RefValue;
use crate::value::Value;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Default)]
pub struct LocalEnv {
    // value(depth, index) = values[depth - 1][index]
    values: Vec<Rc<RefCell<Vec<Value>>>>,
    rec_values: Vec<Rc<[RecValue]>>,
}

#[derive(Debug)]
pub struct RecValue {
    lambda_def: Rc<LambdaDef>,
    env: std::rc::Weak<LocalEnv>,
}

impl PartialEq for RecValue {
    fn eq(&self, rhs: &RecValue) -> bool {
        self.lambda_def == rhs.lambda_def && self.env.as_ptr() == rhs.env.as_ptr()
    }
}
impl Eq for RecValue {}

impl LocalEnv {
    pub fn new() -> LocalEnv {
        Default::default()
    }
    pub fn extended(&self, args: Rc<RefCell<Vec<Value>>>) -> LocalEnv {
        let mut values = self.values.clone();
        values.push(args);
        let rec_values = self.rec_values.clone();
        LocalEnv { values, rec_values }
    }
    pub fn get(&self, depth: usize, index: usize) -> Value {
        self.values[depth - 1].as_ref().borrow()[index].clone()
    }
    pub fn set(&self, depth: usize, index: usize, value: Value) {
        let mut v = self.values[depth - 1].as_ref().borrow_mut();
        v[index] = value;
    }
    pub fn get_rec(&self, rec_depth: usize, index: usize) -> Value {
        let rec_value = &self.rec_values[rec_depth - 1].as_ref()[index];
        let env = rec_value
            .env
            .upgrade()
            .expect("LambdaDef's env must alive here");
        Value::ref_value(RefValue::RecLambda {
            lambda_def: rec_value.lambda_def.clone(),
            env,
        })
    }
    pub fn rec_extended(&self, defs: &[LambdaDef]) -> Rc<LocalEnv> {
        let values = self.values.clone();
        let rec_values = self.rec_values.clone();
        let env = Rc::new(LocalEnv { values, rec_values });
        let self_ref = Rc::downgrade(&env);
        let additional = defs
            .iter()
            .map(|def| RecValue {
                lambda_def: Rc::new(def.clone()),
                env: self_ref.clone(),
            })
            .collect::<Vec<_>>();
        let additional = Rc::from(additional);
        unsafe {
            let rec_values = &env.as_ref().rec_values as *const _ as *mut Vec<Rc<[RecValue]>>;
            (*rec_values).push(additional);
        }
        env
    }
}
