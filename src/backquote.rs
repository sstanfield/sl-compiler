use slvm::error::*;
use slvm::heap::Object;
use slvm::interner::Interned;
use slvm::value::*;
use slvm::vm::*;

use crate::compile::*;
use crate::state::*;

macro_rules! is_tag {
    ($vm:expr, $exp:expr, $form:expr) => {{
        if let Value::Reference(h) = $exp {
            match $vm.get(h) {
                Object::Pair(car, _cdr, _) => {
                    if car.is_symbol($form) {
                        return true;
                    }
                }
                Object::Vector(v) => {
                    if let Some(car) = v.get(0) {
                        if car.is_symbol($form) {
                            return true;
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }};
}

macro_rules! get_data {
    ($vm:expr, $exp:expr) => {{
        if let Value::Reference(h) = $exp {
            match $vm.get(h) {
                Object::Pair(_car, Value::Reference(h), meta) => {
                        if let Object::Pair(ncar, ncdr, _) = $vm.get(*h) {
                            if ncdr.is_nil() {
                                return Ok(*ncar);
                            } else {
                                if let Some(meta) = meta {
                                    return Err(VMError::new_compile(format!(
                                        "Invalid tag at {}:{}, takes one expression.",
                                        meta.line, meta.col
                                    )));
                                } else {
                                    return Err(VMError::new_compile(
                                        "Invalid tag, takes one expression.",
                                    ));
                                }
                            }
                        }
                }
                Object::Vector(v) => {
                    if v.len() != 2 {
                        return Err(VMError::new_compile("Invalid tag, takes one expression."));
                    }
                    return Ok(v[1]);
                }
                _ => {}
            }
        }
        Err(VMError::new_compile("Invalid tag, takes one expression."))
    }};
}

pub struct Tag {
    backquote: Interned,
    unquote: Interned,
    splice: Interned,
    splice_bang: Interned,
}

impl Tag {
    pub fn new(vm: &mut Vm) -> Self {
        Tag {
            backquote: vm.intern("back-quote"),
            unquote: vm.intern("unquote"),
            splice: vm.intern("unquote-splice"),
            splice_bang: vm.intern("unquote-splice!"),
        }
    }

    pub fn is_backquote(&self, vm: &Vm, exp: Value) -> bool {
        is_tag!(vm, exp, self.backquote)
    }

    pub fn is_unquote(&self, vm: &Vm, exp: Value) -> bool {
        is_tag!(vm, exp, self.unquote)
    }

    pub fn is_splice(&self, vm: &Vm, exp: Value) -> bool {
        is_tag!(vm, exp, self.splice)
    }

    pub fn is_splice_bang(&self, vm: &Vm, exp: Value) -> bool {
        is_tag!(vm, exp, self.splice_bang)
    }

    pub fn data(vm: &Vm, exp: Value) -> VMResult<Value> {
        get_data!(vm, exp)
    }
}

fn quote(vm: &mut Vm, exp: Value) -> Value {
    let cdr = Value::Reference(vm.alloc(Object::Pair(exp, Value::Nil, None)));
    let q_i = vm.intern("quote");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), cdr, None)))
}

fn list(vm: &mut Vm, exp: Value) -> Value {
    let cdr = Value::Reference(vm.alloc(Object::Pair(exp, Value::Nil, None)));
    let q_i = vm.intern("list");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), cdr, None)))
}

fn append(vm: &mut Vm, exp1: Value, exp2: Value) -> Value {
    let cdr1 = Value::Reference(vm.alloc(Object::Pair(exp2, Value::Nil, None)));
    let cdr2 = Value::Reference(vm.alloc(Object::Pair(exp1, cdr1, None)));
    let q_i = vm.intern("list-append");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), cdr2, None)))
}

fn qq_expand(
    vm: &mut Vm,
    exp: Value,
    line: &mut u32,
) -> VMResult<Value> {
    let tag = Tag::new(vm);
    if tag.is_unquote(vm, exp) {
        Ok(Tag::data(vm, exp)?)
    } else if tag.is_splice(vm, exp) {
        Err(VMError::new_compile(format!(
            ",@ not valid here: line {}",
            line
        )))
    } else if tag.is_splice_bang(vm, exp) {
        Err(VMError::new_compile(format!(
            ",. not valid here: line {}",
            line
        )))
    } else if tag.is_backquote(vm, exp) {
        let inner = qq_expand(vm, Tag::data(vm, exp)?, line)?;
        Ok(qq_expand(vm, inner, line)?)
    } else {
        match exp {
            Value::Reference(h) => match vm.get(h) {
                Object::Pair(car, cdr, _meta) => {
                    let car = *car;
                    let cdr = *cdr;
                    let l1 = qq_expand_list(vm, car, line)?;
                    //let l1 = qq_expand(vm, car, line)?;
                    let l2 = qq_expand(vm, cdr, line)?;
                    Ok(append(vm, l1, l2))
                }
                Object::Vector(_v) => Ok(Value::Nil),
                _ => Ok(quote(vm, exp)),
            },
            _ => Ok(quote(vm, exp)),
        }
    }
}

fn qq_expand_list(
    vm: &mut Vm,
    exp: Value,
    line: &mut u32,
) -> VMResult<Value> {
    let tag = Tag::new(vm);
    if tag.is_unquote(vm, exp) {
        let data = Tag::data(vm, exp)?;
        Ok(list(vm, data))
    } else if tag.is_splice(vm, exp) || tag.is_splice_bang(vm, exp) {
        Ok(Tag::data(vm, exp)?)
    } else if tag.is_backquote(vm, exp) {
        let inner = qq_expand(vm, Tag::data(vm, exp)?, line)?;
        Ok(qq_expand_list(vm, inner, line)?)
    } else {
        match exp {
            Value::Reference(h) => match vm.get(h) {
                Object::Pair(car, cdr, _meta) => {
                    let car = *car;
                    let cdr = *cdr;
                    let l1 = qq_expand_list(vm, car, line)?;
                    let l2 = qq_expand(vm, cdr, line)?;
                    let app = append(vm, l1, l2);
                    Ok(list(vm, app))
                }
                Object::Vector(_v) => Ok(Value::Nil),
                _ => {
                    let q = quote(vm, exp);
                    Ok(list(vm, q))
                }
            },
            _ => {
                let q = quote(vm, exp);
                Ok(list(vm, q))
            }
        }
    }
}

pub fn backquote(
    vm: &mut Vm,
    state: &mut CompileState,
    exp: Value,
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let exp = qq_expand(vm, exp, line)?;
    pass1(vm, state, exp)?;
    compile(vm, state, exp, result, line)?;
    Ok(())
}
