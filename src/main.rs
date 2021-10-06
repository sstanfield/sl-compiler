use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use slvm::chunk::*;
use slvm::error::*;
use slvm::heap::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use sl_compiler::reader::*;

#[derive(Clone, Debug)]
pub struct SymbolsInt {
    pub syms: HashMap<&'static str, usize>,
    count: usize,
}

// symbol name, idx/reg for scope, idx/reg for outer scope
type Captures = Rc<RefCell<Vec<(&'static str, usize, usize)>>>;

#[derive(Clone, Debug)]
pub struct Symbols {
    pub data: Rc<RefCell<SymbolsInt>>,
    outer: Option<Rc<RefCell<Symbols>>>,
    //namespace: Rc<RefCell<Namespace>>,
    captures: Captures,
}

impl Symbols {
    pub fn with_outer(syms: &Option<Symbols>) -> Symbols {
        let data = Rc::new(RefCell::new(SymbolsInt {
            syms: HashMap::new(),
            count: 0,
        }));
        let outer = syms
            .as_ref()
            .map(|lex_syms| Rc::new(RefCell::new(lex_syms.clone())));
        Symbols {
            data,
            outer,
            //namespace,
            captures: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.data.borrow().syms.is_empty()
    }

    pub fn len(&self) -> usize {
        self.data.borrow().syms.len()
    }

    pub fn contains_symbol(&self, key: &str) -> bool {
        self.data.borrow().syms.contains_key(key)
    }

    pub fn can_capture(&self, key: &'static str) -> bool {
        let mut loop_outer = self.outer.clone();
        while let Some(outer) = loop_outer {
            let outer = outer.borrow();
            if outer.contains_symbol(key) {
                return true;
            }
            loop_outer = outer.outer.clone();
        }
        false
    }

    pub fn get_capture_binding(&self, key: &str) -> Option<usize> {
        for cap in &*self.captures.borrow() {
            if cap.0 == key {
                return Some(cap.2);
            }
        }
        None
    }

    pub fn get(&self, key: &str) -> Option<usize> {
        self.data.borrow().syms.get(key).copied()
    }

    pub fn clear(&mut self) {
        self.data.borrow_mut().syms.clear();
    }

    pub fn insert(&mut self, key: &'static str) -> usize {
        let mut data = self.data.borrow_mut();
        let count = data.count;
        data.syms.insert(key, count);
        data.count += 1;
        count
    }

    pub fn insert_capture(&self, vm: &mut Vm, key: &'static str) -> Option<usize> {
        if let Some(idx) = self.data.borrow().syms.get(key) {
            Some(*idx)
        } else {
            if let Some(outer) = &self.outer {
                // Also capture in outer lexical scope or bad things can happen.
                if let Some(outer_idx) = outer.borrow().insert_capture(vm, key) {
                    let mut data = self.data.borrow_mut();
                    let count = data.count;
                    data.syms.insert(key, count);
                    data.count += 1;
                    self.captures.borrow_mut().push((key, count, outer_idx));
                    return Some(count);
                }
            }
            None
        }
    }

    pub fn len_captures(&self) -> usize {
        self.captures.borrow().len()
    }
}

struct CompileState {
    symbols: Rc<RefCell<Symbols>>,
    chunk: Chunk,
}

fn pr(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    for v in registers {
        print!("{}", v.display_value(vm));
    }
    Ok(Value::Nil)
}

fn prn(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    for v in registers {
        print!("{}", v.display_value(vm));
    }
    println!();
    Ok(Value::Nil)
}

fn compile_call(
    vm: &mut Vm,
    state: &mut CompileState,
    callable: Value,
    cdr: &[Value],
    result: usize,
    line: u32,
) -> VMResult<()> {
    let b_reg = result + cdr.len() + 1;
    let const_i = state.chunk.add_constant(callable);
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1)?;
    }
    state
        .chunk
        .encode2(CONST, b_reg as u16, const_i as u16, line)?;
    state
        .chunk
        .encode3(CALL, b_reg as u16, cdr.len() as u16, result as u16, line)?;
    Ok(())
}

fn compile_list(
    vm: &mut Vm,
    state: &mut CompileState,
    car: Value,
    cdr: &[Value],
    result: usize,
) -> VMResult<()> {
    let def = vm.intern("def");
    let do_ = vm.intern("do");
    let add = vm.intern("+");
    let line = 1;
    match car {
        Value::Symbol(i) if i == do_ => {
            for r in cdr.iter() {
                compile(vm, state, *r, result)?;
            }
        }
        Value::Symbol(i) if i == def => {
            if cdr.len() == 2 {
                if let Value::Symbol(si) = cdr[0] {
                    let sym = vm.get_interned(si);
                    compile(vm, state, cdr[1], result + 1)?;
                    let si_const = state.chunk.add_constant(vm.reserve_symbol(sym));
                    state
                        .chunk
                        .encode2(CONST, result as u16, si_const as u16, line)?;
                    state
                        .chunk
                        .encode2(DEF, result as u16, (result + 1) as u16, line)?;
                }
            }
        }
        Value::Symbol(i) if i == add => {
            if cdr.len() == 2 {
                compile(vm, state, cdr[0], result + 1)?;
                compile(vm, state, cdr[1], result + 2)?;
                state.chunk.encode3(
                    ADD,
                    result as u16,
                    (result + 1) as u16,
                    (result + 2) as u16,
                    line,
                )?;
            }
        }
        Value::Symbol(i) => {
            if let Some(global) = vm.intern_to_global(i) {
                match global {
                    Value::Builtin(builtin) => {
                        compile_call(vm, state, Value::Builtin(builtin), cdr, result, line)?
                    }
                    _ => {}
                }
            }
        }
        Value::Builtin(builtin) => compile_call(vm, state, Value::Builtin(builtin), cdr, result, line)?,
        _ => {}
    }
    Ok(())
}

fn compile(vm: &mut Vm, state: &mut CompileState, exp: Value, result: usize) -> VMResult<()> {
    // Need to break the cdr lifetime away from the vm for a call or we have
    // to reallocate stuff for no reason.
    // Should be safe because compiling code should not be manupulating values on
    // the heap (where the underlying vector lives).
    fn make_vec_cdr(cdr: &[Value]) -> &'static [Value] {
        unsafe { &*(cdr as *const [Value]) }
    }
    let line = 1;
    match exp {
        Value::Reference(h) => match vm.get(h) {
            Object::Pair(car, cdr) => {
                let cdr: Vec<Value> = cdr.iter(vm).collect();
                let car = *car;
                compile_list(vm, state, car, &cdr[..], result)?;
            }
            Object::Vector(v) => {
                if let Some(car) = v.get(0) {
                    let car = *car;
                    if v.len() > 1 {
                        let cdr = make_vec_cdr(&v[1..]);
                        compile_list(vm, state, car, cdr, result)?;
                    } else {
                        compile_list(vm, state, car, &[], result)?;
                    }
                }
            }
            _ => {}
        },
        _ => {
            let const_i = state.chunk.add_constant(exp);
            state
                .chunk
                .encode2(CONST, result as u16, const_i as u16, line)?;
        }
    }
    Ok(())
}

fn main() {
    let mut vm = Vm::new();
    vm.set_global("pr", Value::Builtin(pr));
    vm.set_global("prn", Value::Builtin(prn));
    let mut reader_state = ReaderState::new();
    let mut state = CompileState {
        symbols: Rc::new(RefCell::new(Symbols::with_outer(&None))),
        chunk: Chunk::new("no_file", 1),
    };
    let txt = "(do (pr \"Hello World!\n\n\")(prn \"hello: \"(def xxx (def yyy (+ 3 2)))))";
    let exp = read(&mut vm, &mut reader_state, txt, None, false).unwrap();
    compile(&mut vm, &mut state, exp, 0).unwrap();
    state.chunk.encode0(RET, 1).unwrap();
    println!("Compile: {}", txt);
    vm.dump_globals();
    state.chunk.disassemble_chunk(&vm).unwrap();
    let chunk = Rc::new(state.chunk);
    vm.execute(chunk.clone()).unwrap();
    println!("\n\nPOST exec:\n");
    vm.dump_globals();
    chunk.disassemble_chunk(&vm).unwrap();
}
