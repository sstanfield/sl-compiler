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
    let q_i = vm.intern_static("quote");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), cdr, None)))
}

fn list(vm: &mut Vm, exp: Value) -> Value {
    let cdr = Value::Reference(vm.alloc(Object::Pair(exp, Value::Nil, None)));
    let q_i = vm.intern_static("list");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), cdr, None)))
}

fn vec(vm: &mut Vm, v: &[Value]) -> Value {
    let mut last_pair = Value::Nil;
    if !v.is_empty() {
        let mut i = v.len();
        while i > 0 {
            let obj = Object::Pair(v[i - 1], last_pair, None);
            last_pair = Value::Reference(vm.alloc(obj));
            i -= 1;
        }
    }
    let q_i = vm.intern_static("vec");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), last_pair, None)))
}

fn list2(vm: &mut Vm, exp: Value) -> Value {
    let q_i = vm.intern_static("list");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), exp, None)))
}

fn append(vm: &mut Vm, exp1: Value, exp2: Value) -> Value {
    let cdr1 = Value::Reference(vm.alloc(Object::Pair(exp2, Value::Nil, None)));
    let cdr2 = Value::Reference(vm.alloc(Object::Pair(exp1, cdr1, None)));
    let q_i = vm.intern_static("list-append");
    Value::Reference(vm.alloc(Object::Pair(Value::Symbol(q_i), cdr2, None)))
}

fn rewrap(vm: &mut Vm, exp: Value, sym: &'static str) -> Value {
    let cdr = Value::Reference(vm.alloc(Object::Pair(exp, Value::Nil, None)));
    let q_i = vm.intern_static(sym);
    let obj = Object::Pair(quote(vm, Value::Symbol(q_i)), cdr, None);
    let cdr = Value::Reference(vm.alloc(obj));
    list2(vm, cdr)
}

fn unquote(vm: &mut Vm, exp: Value) -> Value {
    rewrap(vm, exp, "unquote")
}

fn splice(vm: &mut Vm, exp: Value) -> Value {
    rewrap(vm, exp, "unquote-splice")
}

fn splice_bang(vm: &mut Vm, exp: Value) -> Value {
    rewrap(vm, exp, "unquote-splice!")
}

fn back_quote(vm: &mut Vm, exp: Value) -> Value {
    rewrap(vm, exp, "back-quote")
}

// Algorithm initially from
// https://3e8.org/pub/scheme/doc/Quasiquotation%20in%20Lisp%20(Bawden).pdf
fn qq_expand(vm: &mut Vm, exp: Value, line: &mut u32, depth: u32) -> VMResult<Value> {
    let tag = Tag::new(vm);
    if tag.is_unquote(vm, exp) {
        if depth == 0 {
            Ok(Tag::data(vm, exp)?)
        } else {
            let expand = qq_expand(vm, Tag::data(vm, exp)?, line, depth - 1)?;
            Ok(unquote(vm, expand))
        }
    } else if tag.is_splice(vm, exp) {
        if depth == 0 {
            Err(VMError::new_compile(format!(
                ",@ not valid here: line {}",
                line
            )))
        } else {
            let expand = qq_expand(vm, Tag::data(vm, exp)?, line, depth - 1)?;
            Ok(splice(vm, expand))
        }
    } else if tag.is_splice_bang(vm, exp) {
        if depth == 0 {
            Err(VMError::new_compile(format!(
                ",. not valid here: line {}",
                line
            )))
        } else {
            let expand = qq_expand(vm, Tag::data(vm, exp)?, line, depth - 1)?;
            Ok(splice_bang(vm, expand))
        }
    } else if tag.is_backquote(vm, exp) {
        let inner = qq_expand(vm, Tag::data(vm, exp)?, line, depth + 1)?;
        Ok(back_quote(vm, inner))
    } else {
        match exp {
            Value::Reference(h) => match vm.get(h) {
                Object::Pair(car, cdr, _meta) => {
                    let car = *car;
                    let cdr = *cdr;
                    let l1 = qq_expand_list(vm, car, line, depth)?;
                    if cdr.is_nil() {
                        Ok(l1)
                    } else {
                        let l2 = qq_expand(vm, cdr, line, depth)?;
                        Ok(append(vm, l1, l2))
                    }
                }
                Object::Vector(vector) => {
                    let mut new_vec: Vec<Value> = vector.iter().copied().collect();
                    for i in &mut new_vec {
                        *i = qq_expand(vm, *i, line, depth)?;
                    }
                    Ok(vec(vm, &new_vec[..]))
                }
                _ => Ok(quote(vm, exp)),
            },
            _ => Ok(quote(vm, exp)),
        }
    }
}

fn qq_expand_list(vm: &mut Vm, exp: Value, line: &mut u32, depth: u32) -> VMResult<Value> {
    let tag = Tag::new(vm);
    if tag.is_unquote(vm, exp) {
        if depth == 0 {
            let data = Tag::data(vm, exp)?;
            Ok(list(vm, data))
        } else {
            let expand = qq_expand(vm, Tag::data(vm, exp)?, line, depth - 1)?;
            let inner = unquote(vm, expand);
            Ok(list(vm, inner))
        }
    } else if tag.is_splice(vm, exp) {
        if depth == 0 {
            Ok(Tag::data(vm, exp)?)
        } else {
            let expand = qq_expand(vm, Tag::data(vm, exp)?, line, depth - 1)?;
            let inner = splice(vm, expand);
            Ok(list(vm, inner))
        }
    } else if tag.is_splice_bang(vm, exp) {
        if depth == 0 {
            Ok(Tag::data(vm, exp)?)
        } else {
            let expand = qq_expand(vm, Tag::data(vm, exp)?, line, depth - 1)?;
            let inner = splice_bang(vm, expand);
            Ok(list(vm, inner))
        }
    } else if tag.is_backquote(vm, exp) {
        let inner = qq_expand(vm, Tag::data(vm, exp)?, line, depth + 1)?;
        let inner = back_quote(vm, inner);
        Ok(list(vm, inner))
    } else {
        match exp {
            Value::Reference(h) => match vm.get(h) {
                Object::Pair(car, cdr, _meta) => {
                    let car = *car;
                    let cdr = *cdr;
                    let l1 = qq_expand_list(vm, car, line, depth)?;
                    if cdr.is_nil() {
                        Ok(list(vm, l1))
                    } else {
                        let l2 = qq_expand(vm, cdr, line, depth)?;
                        let app = append(vm, l1, l2);
                        Ok(list(vm, app))
                    }
                }
                Object::Vector(vector) => {
                    let mut new_vec: Vec<Value> = vector.iter().copied().collect();
                    for i in &mut new_vec {
                        *i = qq_expand(vm, *i, line, depth)?;
                    }
                    let vv = vec(vm, &new_vec[..]);
                    Ok(list(vm, vv))
                }
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
    let exp = qq_expand(vm, exp, line, 0)?;
    //println!("XXXX {}", exp.display_value(vm));
    pass1(vm, state, exp)?;
    compile(vm, state, exp, result, line)?;
    Ok(())
}
