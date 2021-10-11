use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use slvm::chunk::*;
use slvm::error::*;
use slvm::heap::*;
use slvm::interner::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use sl_compiler::reader::*;

#[derive(Clone, Debug)]
pub struct SymbolsInt {
    pub syms: HashMap<Interned, usize, BuildInternedHasher>,
    count: usize,
}

impl SymbolsInt {
    pub fn add_sym(&mut self, sym: Interned) {
        self.syms.insert(sym, self.count);
        self.count += 1;
    }
}

// symbol name, idx/reg for scope, idx/reg for outer scope
type Captures = Rc<RefCell<Vec<(Interned, usize, usize)>>>;

#[derive(Clone, Debug)]
pub struct Symbols {
    pub data: Rc<RefCell<SymbolsInt>>,
    outer: Option<Rc<RefCell<Symbols>>>,
    //namespace: Rc<RefCell<Namespace>>,
    captures: Captures,
}

impl Symbols {
    pub fn with_outer(outer: Option<Rc<RefCell<Symbols>>>) -> Symbols {
        let data = Rc::new(RefCell::new(SymbolsInt {
            syms: HashMap::with_hasher(BuildInternedHasher::new()),
            count: 0,
        }));
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

    pub fn contains_symbol(&self, key: Interned) -> bool {
        self.data.borrow().syms.contains_key(&key)
    }

    pub fn can_capture(&self, key: Interned) -> bool {
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

    pub fn get_capture_binding(&self, key: Interned) -> Option<usize> {
        for cap in &*self.captures.borrow() {
            if cap.0 == key {
                return Some(cap.2);
            }
        }
        None
    }

    pub fn get(&self, key: Interned) -> Option<usize> {
        self.data.borrow().syms.get(&key).copied()
    }

    pub fn clear(&mut self) {
        self.data.borrow_mut().syms.clear();
    }

    pub fn insert(&mut self, key: Interned) -> usize {
        let mut data = self.data.borrow_mut();
        let count = data.count;
        data.syms.insert(key, count);
        data.count += 1;
        count
    }

    pub fn insert_capture(&self, vm: &mut Vm, key: Interned) -> Option<usize> {
        if let Some(idx) = self.data.borrow().syms.get(&key) {
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

impl CompileState {
    pub fn reserved_regs(&self) -> usize {
        self.symbols.borrow().len() + 1
    }

    pub fn get_symbol(&self, sym: Interned) -> Option<usize> {
        self.symbols.borrow().data.borrow().syms.get(&sym).copied()
    }
}

fn pr(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    for v in registers {
        print!("{}", v.pretty_value(vm));
    }
    Ok(Value::Nil)
}

fn prn(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    for v in registers {
        print!("{}", v.pretty_value(vm));
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

fn compile_callg(
    vm: &mut Vm,
    state: &mut CompileState,
    global: u32,
    cdr: &[Value],
    result: usize,
    line: u32,
) -> VMResult<()> {
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1)?;
    }
    state
        .chunk
        .encode_callg(global, cdr.len() as u16, result as u16, line)?;
    Ok(())
}

fn compile_call_reg(
    vm: &mut Vm,
    state: &mut CompileState,
    reg: u16,
    cdr: &[Value],
    result: usize,
    line: u32,
) -> VMResult<()> {
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1)?;
    }
    state
        .chunk
        .encode3(CALL, reg, cdr.len() as u16, result as u16, line)?;
    Ok(())
}

fn compile_fn(
    vm: &mut Vm,
    state: &mut CompileState,
    args: Value,
    cdr: &[Value],
    result: usize,
    line: u32,
) -> VMResult<()> {
    if let Value::Reference(h) = args {
        let obj = vm.get(h);
        let args_iter = match obj {
            Object::Pair(_car, _cdr) => args.iter(vm),
            Object::Vector(_v) => args.iter(vm),
            _ => {
                return Err(VMError::new_compile(format!(
                    "Malformed fn, invalid args, {:?}.",
                    obj
                )));
            }
        };
        let symbols = Symbols::with_outer(Some(state.symbols.clone()));
        for a in args_iter {
            if let Value::Symbol(i) = a {
                symbols.data.borrow_mut().add_sym(i);
            } else {
                return Err(VMError::new_compile(
                    "Malformed fn, invalid args, must be symbols.",
                ));
            }
        }
        let mut new_state = CompileState {
            symbols: Rc::new(RefCell::new(symbols)),
            chunk: Chunk::new("no_file", 1),
        };
        let reserved = new_state.reserved_regs();
        for r in cdr.iter() {
            compile(vm, &mut new_state, *r, reserved)?;
        }
        new_state.chunk.encode1(SRET, reserved as u16, 1).unwrap();
        let lambda = Value::Reference(vm.alloc(Object::Lambda(Rc::new(new_state.chunk))));
        let const_i = state.chunk.add_constant(lambda);
        state
            .chunk
            .encode2(CONST, result as u16, const_i as u16, line)?;
    } else {
        return Err(VMError::new_compile(format!(
            "Malformed fn, invalid args, {:?}.",
            args
        )));
    }
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
    let set = vm.intern("set!");
    let do_ = vm.intern("do");
    let fn_ = vm.intern("fn");
    let add = vm.intern("+");
    let sub = vm.intern("-");
    let mul = vm.intern("*");
    let div = vm.intern("/");
    let line = 1;
    match car {
        Value::Symbol(i) if i == fn_ => {
            if cdr.len() > 1 {
                compile_fn(vm, state, cdr[0], &cdr[1..], result, line)?
            } else {
                return Err(VMError::new_compile("Malformed fn form."));
            }
        }
        Value::Symbol(i) if i == do_ => {
            for r in cdr.iter() {
                compile(vm, state, *r, result)?;
            }
        }
        Value::Symbol(i) if i == def => {
            if cdr.len() == 2 {
                if let Value::Symbol(si) = cdr[0] {
                    compile(vm, state, cdr[1], result + 1)?;
                    let si_const = vm.reserve_index(si);
                    state.chunk.encode_refi(result as u16, si_const, line)?;
                    state
                        .chunk
                        .encode2(DEF, result as u16, (result + 1) as u16, line)?;
                } else {
                    return Err(VMError::new_compile("def: expected symbol"));
                }
            } else {
                return Err(VMError::new_compile("def: malformed"));
            }
        }
        Value::Symbol(i) if i == set => {
            if cdr.len() == 2 {
                if let Value::Symbol(si) = cdr[0] {
                    if let Some(idx) = state.get_symbol(si) {
                        compile(vm, state, cdr[1], result)?;
                        state
                            .chunk
                            .encode2(SET, (idx + 1) as u16, result as u16, line)?;
                    } else {
                        compile(vm, state, cdr[1], result + 1)?;
                        let si_const = vm.reserve_index(si);
                        state.chunk.encode_refi(result as u16, si_const, line)?;
                        state
                            .chunk
                            .encode2(DEF, result as u16, (result + 1) as u16, line)?;
                    }
                } else {
                    return Err(VMError::new_compile("set!: expected symbol"));
                }
            } else {
                return Err(VMError::new_compile("set!: malformed"));
            }
        }
        Value::Symbol(i) if i == add => {
            if cdr.is_empty() {
                compile(vm, state, Value::Int(0), result)?;
            } else if cdr.len() == 1 {
                compile(vm, state, cdr[0], result)?;
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1)?;
                        state.chunk.encode3(
                            ADDM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            line,
                        )?;
                    } else {
                        compile(vm, state, *v, result)?;
                    }
                }
            }
        }
        Value::Symbol(i) if i == sub => {
            if cdr.is_empty() {
                return Err(VMError::new_compile(
                    "Malformed -, requires at least one argument.",
                ));
            } else if cdr.len() == 1 {
                if let Ok(i) = cdr[0].get_int() {
                    compile(vm, state, Value::Int(-i), result)?;
                } else if let Ok(f) = cdr[0].get_float() {
                    compile(vm, state, Value::Float(-f), result)?;
                }
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1)?;
                        state.chunk.encode3(
                            SUBM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            line,
                        )?;
                    } else {
                        compile(vm, state, *v, result)?;
                    }
                }
            }
        }
        Value::Symbol(i) if i == mul => {
            if cdr.is_empty() {
                compile(vm, state, Value::Int(1), result)?;
            } else if cdr.len() == 1 {
                compile(vm, state, cdr[0], result)?;
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1)?;
                        state.chunk.encode3(
                            MULM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            line,
                        )?;
                    } else {
                        compile(vm, state, *v, result)?;
                    }
                }
            }
        }
        Value::Symbol(i) if i == div => {
            if cdr.len() <= 1 {
                return Err(VMError::new_compile(
                    "Malformed /, requires at least two arguments.",
                ));
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1)?;
                        state.chunk.encode3(
                            DIVM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            line,
                        )?;
                    } else {
                        compile(vm, state, *v, result)?;
                    }
                }
            }
        }
        Value::Symbol(i) => {
            if let Some(idx) = state.get_symbol(i) {
                compile_call_reg(vm, state, (idx + 1) as u16, cdr, result, line)?
            } else {
                let slot = vm.reserve_index(i);
                // Is a global so set up a call and will error at runtime if
                // not callable (dynamic is fun).
                if let Value::Undefined = vm.get_global(slot) {
                    eprintln!("Warning: {} not defined.", vm.get_interned(i));
                }
                compile_callg(vm, state, slot as u32, cdr, result, line)?
            }
        }
        Value::Builtin(builtin) => {
            compile_call(vm, state, Value::Builtin(builtin), cdr, result, line)?
        }
        Value::Reference(h) => {
            if let Object::Lambda(_) = vm.get(h) {
                compile_call(vm, state, Value::Reference(h), cdr, result, line)?
            }
        }
        _ => {
            println!("Boo");
        }
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
        Value::Symbol(i) => {
            if let Some(idx) = state.get_symbol(i) {
                state
                    .chunk
                    .encode2(MOV, result as u16, (idx + 1) as u16, line)?;
            } else {
                let const_i = vm.reserve_index(i);
                state.chunk.encode_refi(result as u16, const_i, line)?;
            }
        }
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
        symbols: Rc::new(RefCell::new(Symbols::with_outer(None))),
        chunk: Chunk::new("no_file", 1),
    };
    let txt = "(do
    (pr \"Hello World!\n\")
    (prn \"hello: \"(def xxx (def yyy (+ 3 2))))
    (def fn1 (fn (a) (prn \"FUNC\" a)(prn (a 10))))
    (fn1 (fn (x) (set! x (+ x 2))(+ x 1)))
    (def fn2 (fn (x y) (set! x (+ x 1))(set! y (+ y 1))(+ x y)))
    (prn \"am i 7? \" (fn2 2 3))
    (def xx 5)(prn \"xx: \" xx)
    (def fn3 (fn (y) (set! xx (+ xx 1))(set! y (+ y 1))(+ xx y)))
    (prn \"am i 10? \" (fn3 3) \" \" xx)
    (prn \"xx: \" xx)
    (def xx 7)(prn \"xx: \" xx)
    (prn \"am i 10? \" (fn3 3) \" \" xx)
    (prn \"am i 15? \" (+ 10 3 2))
    (prn \"am i 12? \" (+ 12))
    (prn \"am i 0? \" (+))
    (prn \"am i -5? \" (- 5))
    (prn \"am i 1? \" (- 9 8))
    (prn \"am i 0? \" (- 9 8 1))
    (prn \"am i 1? \" (*))
    (prn \"am i 5? \" (* 5))
    (prn \"am i 15? \" (* 3 5))
    (prn \"am i 15? \" (* 3 5))
    (prn \"am i 30? \" (* 3 5 2))
    (prn \"am i 3? \" (/ 15 5))
    )";
    let exp = read(&mut vm, &mut reader_state, txt, None, false).unwrap();
    compile(&mut vm, &mut state, exp, 0).unwrap();
    state.chunk.encode0(RET, 1).unwrap();
    println!("Compile: {}", txt);
    vm.dump_globals();
    state.chunk.disassemble_chunk(&vm).unwrap();
    let chunk = Rc::new(state.chunk.clone());
    if let Err(err) = vm.execute(chunk) {
        println!("ERROR: {}", err);
        vm.dump_globals();
        state.chunk.disassemble_chunk(&vm).unwrap();
    }
    //println!("\n\nPOST exec:\n");
    //vm.dump_globals();
    //chunk.disassemble_chunk(&vm).unwrap();
}
