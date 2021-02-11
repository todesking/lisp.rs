use crate::value::LambdaDef;
use crate::value::RefValue;
use crate::value::Value;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub enum LocalEnv {
    Local {
        depth: usize,
        values: Rc<RefCell<Vec<Value>>>,
        parent: Option<Rc<LocalEnv>>,
    },
    Rec {
        rec_depth: usize,
        rec_values: Vec<RecValue>,
        parent: Option<Rc<LocalEnv>>,
    },
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
    // for testing :(
    pub fn any() -> LocalEnv {
        LocalEnv::Local {
            values: Default::default(),
            depth: 1,
            parent: None,
        }
    }
    pub fn extended(
        parent: Option<Rc<LocalEnv>>,
        depth: usize,
        values: Rc<RefCell<Vec<Value>>>,
    ) -> Rc<LocalEnv> {
        Rc::new(LocalEnv::Local {
            depth,
            values,
            parent,
        })
    }
    pub fn get(env: &Option<Rc<LocalEnv>>, depth: usize, index: usize) -> Value {
        if let Some(env) = env {
            let target_depth = depth;
            match env.as_ref() {
                LocalEnv::Local {
                    values,
                    depth,
                    parent,
                } => {
                    if *depth == target_depth {
                        values.borrow()[index].clone()
                    } else {
                        Self::get(parent, target_depth, index)
                    }
                }
                LocalEnv::Rec { parent, .. } => Self::get(parent, depth, index),
            }
        } else {
            panic!(format!(
                "get: Local variable lookup failed: depth={}, index={}",
                depth, index
            ))
        }
    }
    pub fn set(env: &Option<Rc<LocalEnv>>, depth: usize, index: usize, value: Value) {
        if let Some(env) = env {
            let target_depth = depth;
            match env.as_ref() {
                LocalEnv::Local {
                    values,
                    depth,
                    parent,
                } => {
                    if *depth == target_depth {
                        values.borrow_mut()[index] = value;
                    } else {
                        Self::set(parent, target_depth, index, value)
                    }
                }
                LocalEnv::Rec { parent, .. } => Self::set(parent, depth, index, value),
            }
        } else {
            panic!(format!(
                "set: Local variable lookup failed: depth={}, index={}",
                depth, index
            ))
        }
    }
    pub fn get_rec(env: &Option<Rc<LocalEnv>>, rec_depth: usize, index: usize) -> Value {
        if let Some(env) = env {
            let target_depth = rec_depth;
            match env.as_ref() {
                LocalEnv::Rec {
                    rec_depth,
                    rec_values,
                    parent,
                } => {
                    if *rec_depth == target_depth {
                        let rec_value = &rec_values[index];
                        let env = rec_value
                            .env
                            .upgrade()
                            .expect("LambdaDef's env must alive here");
                        Value::ref_value(RefValue::RecLambda {
                            lambda_def: rec_value.lambda_def.clone(),
                            env,
                        })
                    } else {
                        Self::get_rec(parent, target_depth, index)
                    }
                }
                LocalEnv::Local { parent, .. } => Self::get_rec(parent, target_depth, index),
            }
        } else {
            panic!(format!(
                "get_rec: Local variable lookup failed: rec_depth={}, index={}",
                rec_depth, index
            ))
        }
    }
    pub fn rec_extended(
        parent: Option<Rc<LocalEnv>>,
        rec_depth: usize,
        defs: &[LambdaDef],
    ) -> Rc<LocalEnv> {
        let env = LocalEnv::Rec {
            rec_depth,
            rec_values: Vec::with_capacity(defs.len()),
            parent,
        };
        let env = Rc::new(env);
        let self_ref = Rc::downgrade(&env);
        let rvs = defs
            .iter()
            .map(|def| RecValue {
                lambda_def: Rc::new(def.clone()),
                env: self_ref.clone(),
            })
            .collect::<Vec<_>>();
        unsafe {
            match env.as_ref() {
                LocalEnv::Rec { rec_values, .. } => {
                    let rec_values = rec_values as *const _ as *mut Vec<RecValue>;
                    for rv in rvs {
                        (*rec_values).push(rv);
                    }
                }
                LocalEnv::Local { .. } => unreachable!(),
            }
        }
        env
    }
}
