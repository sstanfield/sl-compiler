use slvm::error::*;
use slvm::interner::Interned;
use slvm::value::*;
use slvm::vm::*;

use crate::compile::*;
use crate::state::*;

macro_rules! is_tag {
    ($vm:expr, $exp:expr, $form:expr) => {{
        match $exp {
            Value::Pair(handle) => {
                let (car, _) = $vm.get_pair(handle);
                if car.is_symbol($form) {
                    return true;
                }
            }
            Value::Vector(handle) => {
                let v = $vm.get_vector(handle);
                if let Some(car) = v.get(0) {
                    if car.is_symbol($form) {
                        return true;
                    }
                }
            }
            _ => {}
        }
        false
    }};
}

macro_rules! get_data {
    ($vm:expr, $exp:expr) => {{
        match $exp {
            Value::Pair(handle) => {
                let (_, cdr) = $vm.get_pair(handle);
                if let Value::Pair(cdr_handle) = cdr {
                    let (ncar, ncdr) = $vm.get_pair(cdr_handle);
                    if ncdr.is_nil() {
                        return Ok(ncar);
                    } else {
                        let (line, col) = (
                            $vm.get_heap_property(handle, ":dbg-line"),
                            $vm.get_heap_property(handle, ":dbg-col"),
                        );
                        if let (Some(Value::UInt(line)), Some(Value::UInt(col))) = (line, col) {
                            return Err(VMError::new_compile(format!(
                                "Invalid tag at {}:{}, takes one expression.",
                                line, col
                            )));
                        } else {
                            return Err(VMError::new_compile("Invalid tag, takes one expression."));
                        }
                    }
                }
            }
            Value::Vector(handle) => {
                let v = $vm.get_vector(handle);
                if v.len() != 2 {
                    return Err(VMError::new_compile("Invalid tag, takes one expression."));
                }
                return Ok(v[1]);
            }
            _ => {}
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
    let cdr = vm.alloc_pair(exp, Value::Nil);
    let q_i = vm.intern_static("quote");
    vm.alloc_pair(Value::Symbol(q_i), cdr)
}

fn list(vm: &mut Vm, exp: Value) -> Value {
    let cdr = vm.alloc_pair(exp, Value::Nil);
    let q_i = vm.intern_static("list");
    vm.alloc_pair(Value::Symbol(q_i), cdr)
}

fn vec(vm: &mut Vm, v: &[Value]) -> Value {
    let mut last_pair = Value::Nil;
    if !v.is_empty() {
        let mut i = v.len();
        while i > 0 {
            last_pair = vm.alloc_pair(v[i - 1], last_pair);
            i -= 1;
        }
    }
    let q_i = vm.intern_static("vec");
    vm.alloc_pair(Value::Symbol(q_i), last_pair)
}

fn list2(vm: &mut Vm, exp: Value) -> Value {
    let q_i = vm.intern_static("list");
    vm.alloc_pair(Value::Symbol(q_i), exp)
}

fn append(vm: &mut Vm, exp1: Value, exp2: Value) -> Value {
    let cdr1 = vm.alloc_pair(exp2, Value::Nil);
    let cdr2 = vm.alloc_pair(exp1, cdr1);
    let q_i = vm.intern_static("list-append");
    vm.alloc_pair(Value::Symbol(q_i), cdr2)
}

fn rewrap(vm: &mut Vm, exp: Value, sym: &'static str) -> Value {
    let cdr = vm.alloc_pair(exp, Value::Nil);
    let q_i = vm.intern_static(sym);
    let car = quote(vm, Value::Symbol(q_i));
    let cdr = vm.alloc_pair(car, cdr);
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
fn qq_expand(vm: &mut Vm, exp: Value, line: u32, depth: u32) -> VMResult<Value> {
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
            Value::Pair(handle) => {
                let (car, cdr) = vm.get_pair(handle);
                let l1 = qq_expand_list(vm, car, line, depth)?;
                if cdr.is_nil() {
                    Ok(l1)
                } else {
                    let l2 = qq_expand(vm, cdr, line, depth)?;
                    Ok(append(vm, l1, l2))
                }
            }
            Value::Vector(handle) => {
                let vector = vm.get_vector(handle);
                let mut new_vec: Vec<Value> = vector.to_vec();
                for i in &mut new_vec {
                    *i = qq_expand(vm, *i, line, depth)?;
                }
                Ok(vec(vm, &new_vec[..]))
            }
            _ => Ok(quote(vm, exp)),
        }
    }
}

fn qq_expand_list(vm: &mut Vm, exp: Value, line: u32, depth: u32) -> VMResult<Value> {
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
            Value::Pair(handle) => {
                let (car, cdr) = vm.get_pair(handle);
                let l1 = qq_expand_list(vm, car, line, depth)?;
                if cdr.is_nil() {
                    Ok(list(vm, l1))
                } else {
                    let l2 = qq_expand(vm, cdr, line, depth)?;
                    let app = append(vm, l1, l2);
                    Ok(list(vm, app))
                }
            }
            Value::Vector(handle) => {
                let vector = vm.get_vector(handle);
                let mut new_vec: Vec<Value> = vector.to_vec();
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
        }
    }
}

pub fn backquote(
    vm: &mut Vm,
    state: &mut CompileState,
    exp: Value,
    result: usize,
    line: &mut Option<&mut u32>,
) -> VMResult<()> {
    let line_num = match line {
        Some(l) => **l,
        None => 0,
    };
    let exp = qq_expand(vm, exp, line_num, 0)?;
    pass1(vm, state, exp)?;
    compile(vm, state, exp, result, line)?;
    Ok(())
}
