use crate::ast::VarRef;
use crate::name::AbsName;
use crate::name::MemberName;
use crate::name::Name;
use crate::name::SimpleName;
use crate::GlobalEnv;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct StaticEnv<'a> {
    global: &'a GlobalEnv,
    locals: HashMap<SimpleName, VarRef>,
    new_globals: HashMap<MemberName, usize>,
    local_depth: usize,
    args: Vec<SimpleName>,
    rec_depth: usize,
    current_module: Option<AbsName>,
    imports: HashMap<SimpleName, MemberName>,
    module_members: HashMap<AbsName, HashSet<SimpleName>>,
}
// accessors
impl<'a> StaticEnv<'a> {
    pub fn global(&self) -> &'a GlobalEnv {
        &self.global
    }
    pub fn current_module(&self) -> &Option<AbsName> {
        &self.current_module
    }
    pub fn imports(&self) -> &HashMap<SimpleName, MemberName> {
        &self.imports
    }
    pub fn module_members(&self) -> &HashMap<AbsName, HashSet<SimpleName>> {
        &self.module_members
    }
    pub fn local_depth(&self) -> usize {
        self.local_depth
    }
    pub fn rec_depth(&self) -> usize {
        self.rec_depth
    }
}
// misc
impl<'a> StaticEnv<'a> {
    pub fn new(global: &GlobalEnv) -> StaticEnv {
        Self::new_with_current_module(global, None)
    }
    pub fn new_with_current_module(
        global: &GlobalEnv,
        current_module: Option<AbsName>,
    ) -> StaticEnv {
        StaticEnv {
            global,
            locals: Default::default(),
            new_globals: Default::default(),
            local_depth: 0,
            args: Default::default(),
            rec_depth: 0,
            current_module,
            imports: global.imports().clone(),
            module_members: global.module_members().clone(),
        }
    }
    pub fn new_global(&mut self, name: MemberName) {
        if !self.global_defined(&name) {
            let new_id = self.global.next_id() + self.new_globals.len();
            self.new_globals.insert(name.clone(), new_id);
            self.new_module_member(name.module_name, name.simple_name);
        }
    }
    pub fn new_import(&mut self, name: SimpleName, full_name: MemberName) {
        self.imports.insert(name, full_name);
    }
    pub fn lookup(&self, name: &str) -> Option<VarRef> {
        SimpleName::parse(name)
            .and_then(|name| self.locals.get(&name).cloned())
            .or_else(|| {
                let abs_name = self.resolve_global_name(name)?;
                self.lookup_global_id(&abs_name).map(VarRef::Global)
            })
    }

    fn global_defined(&self, name: &MemberName) -> bool {
        self.lookup_global_id(name).is_some()
    }
    pub fn lookup_global_id(&self, name: &MemberName) -> Option<usize> {
        self.new_globals
            .get(name)
            .cloned()
            .or_else(|| self.global.lookup_global_id(name))
    }
    pub fn extended(
        &self,
        names: impl IntoIterator<Item = SimpleName>,
        rest_name: Option<SimpleName>,
    ) -> StaticEnv<'a> {
        let mut env = self.clone();
        env.local_depth += 1;
        env.args = Default::default();
        for (i, name) in self.args.iter().enumerate() {
            env.locals
                .insert(name.clone(), VarRef::Local(env.local_depth, i));
        }
        for (i, name) in names.into_iter().chain(rest_name.into_iter()).enumerate() {
            env.args.push(name.clone());
            env.locals.insert(name.clone(), VarRef::Argument(i));
        }
        env
    }
    pub fn rec_extended(&self, names: impl IntoIterator<Item = SimpleName>) -> StaticEnv<'a> {
        let mut env = self.clone();
        env.args = Default::default();
        env.local_depth += 1;
        env.rec_depth += 1;
        for (i, name) in self.args.iter().enumerate() {
            env.locals
                .insert(name.clone(), VarRef::Local(env.local_depth, i));
        }
        for (i, name) in names.into_iter().enumerate() {
            env.locals.insert(name, VarRef::Rec(env.rec_depth, i));
        }
        env
    }
    pub fn module_scope<T>(&mut self, mname: AbsName, f: impl FnOnce(&mut StaticEnv) -> T) -> T {
        let imports = self.imports.clone();
        let current_module = self.current_module.clone();
        self.current_module = Some(mname);
        let ret = f(self);
        self.current_module = current_module;
        self.imports = imports;
        ret
    }
    pub fn has_module_member(&self, module_name: AbsName, name: SimpleName) -> bool {
        let member_name = module_name.into_member_name(name);
        // TODO: remove this: every globals should registered by self.module_members
        self.lookup_global_id(&member_name).is_some()
            || self
                .module_members
                .get(&member_name.module_name)
                .map(|names| names.contains(&member_name.simple_name))
                .unwrap_or(false)
    }
    pub fn has_module(&self, mname: &AbsName) -> bool {
        self.module_members.contains_key(mname)
    }
    pub fn new_module_member(&mut self, module_name: AbsName, name: SimpleName) {
        self.module_members
            .entry(module_name)
            .or_insert_with(HashSet::new)
            .insert(name);
    }
    pub fn resolve_global_name(&self, name: &str) -> Option<MemberName> {
        let current_module = self.current_module();
        let imports = self.imports();
        let module_members = self.module_members();

        let name = Name::parse(name)?;
        match name {
            Name::Single(name) => {
                if let Some(current_module) = current_module {
                    if module_members
                        .get(&current_module)
                        .map(|names| names.contains(&name))
                        .unwrap_or(false)
                    {
                        return Some(current_module.member_name(name));
                    }
                }
                if let Some(found) = imports.get(&name) {
                    Some(found.clone())
                } else {
                    // TODO: search global.module_members if current_module = None, else return None
                    let current_module = current_module.clone().unwrap_or_else(AbsName::global);
                    Some(current_module.into_member_name(name))
                }
            }
            Name::Relative(parts, name) => {
                if let Some(prefix) = imports.get(&parts[0]) {
                    Some(
                        prefix
                            .to_abs_name()
                            .into_descendant_name(parts[1..].iter().cloned())
                            .into_member_name(name),
                    )
                } else {
                    let root = current_module.clone().unwrap_or_else(AbsName::root);
                    Some(root.into_descendant_name(parts).into_member_name(name))
                }
            }
            Name::Absolute(name) => Some(name),
        }
    }
}
