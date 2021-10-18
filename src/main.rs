use std::rc::Rc;

use slvm::error::*;
use slvm::heap::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use sl_compiler::config::*;
use sl_compiler::reader::*;
use sl_compiler::state::*;

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
    line: &mut u32,
) -> VMResult<()> {
    let b_reg = result + cdr.len() + 1;
    let const_i = state.add_constant(callable);
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    state
        .chunk
        .encode2(CONST, b_reg as u16, const_i as u16, *line)?;
    state
        .chunk
        .encode3(CALL, b_reg as u16, cdr.len() as u16, result as u16, *line)?;
    Ok(())
}

fn compile_callg(
    vm: &mut Vm,
    state: &mut CompileState,
    global: u32,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    state
        .chunk
        .encode_callg(global, cdr.len() as u16, result as u16, *line)?;
    Ok(())
}

fn compile_call_reg(
    vm: &mut Vm,
    state: &mut CompileState,
    reg: u16,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    state
        .chunk
        .encode3(CALL, reg, cdr.len() as u16, result as u16, *line)?;
    Ok(())
}

fn compile_fn(
    vm: &mut Vm,
    state: &mut CompileState,
    args: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let mut new_state = match args {
        Value::Reference(h) => {
            let obj = vm.get(h);
            let args_iter = match obj {
                Object::Pair(_car, _cdr, meta) => {
                    if let Some(meta) = meta {
                        *line = meta.line as u32;
                    }
                    args.iter(vm)
                }
                Object::Vector(_v) => args.iter(vm),
                _ => {
                    return Err(VMError::new_compile(format!(
                        "Malformed fn, invalid args, {:?}.",
                        obj
                    )));
                }
            };
            let new_state =
                CompileState::new_state(state.chunk.file_name, *line, Some(state.symbols.clone()));
            for a in args_iter {
                if let Value::Symbol(i) = a {
                    new_state.symbols.borrow_mut().data.borrow_mut().add_sym(i);
                } else {
                    return Err(VMError::new_compile(
                        "Malformed fn, invalid args, must be symbols.",
                    ));
                }
            }
            new_state
        }
        Value::Nil => {
            CompileState::new_state(state.chunk.file_name, *line, Some(state.symbols.clone()))
        }
        _ => {
            return Err(VMError::new_compile(format!(
                "Malformed fn, invalid args, {:?}.",
                args
            )))
        }
    };
    for r in cdr.iter() {
        pass1(vm, &mut new_state, *r).unwrap();
    }
    let reserved = new_state.reserved_regs();
    for r in cdr.iter() {
        compile(vm, &mut new_state, *r, reserved, line)?;
    }
    new_state
        .chunk
        .encode1(SRET, reserved as u16, *line)
        .unwrap();
    let mut closure = false;
    if !new_state.symbols.borrow().captures.borrow().is_empty() {
        let mut caps = Vec::new();
        for (_, _, c) in new_state.symbols.borrow().captures.borrow().iter() {
            caps.push((*c + 1) as u32);
        }
        new_state.chunk.captures = Some(caps);
        closure = true;
    }
    let lambda = Value::Reference(vm.alloc(Object::Lambda(Rc::new(new_state.chunk))));
    let const_i = state.add_constant(lambda);
    state
        .chunk
        .encode2(CONST, result as u16, const_i as u16, *line)?;
    if closure {
        state
            .chunk
            .encode2(CLOSE, result as u16, result as u16, *line)?;
    }
    Ok(())
}

fn compile_list(
    vm: &mut Vm,
    state: &mut CompileState,
    car: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let def = vm.intern("def");
    let set = vm.intern("set!");
    let do_ = vm.intern("do");
    let fn_ = vm.intern("fn");
    let if_ = vm.intern("if");
    let add = vm.intern("+");
    let sub = vm.intern("-");
    let mul = vm.intern("*");
    let div = vm.intern("/");
    let inc = vm.intern("inc!");
    let dec = vm.intern("dec!");
    match car {
        Value::Symbol(i) if i == fn_ => {
            if cdr.len() > 1 {
                compile_fn(vm, state, cdr[0], &cdr[1..], result, line)?
            } else {
                return Err(VMError::new_compile("Malformed fn form."));
            }
        }
        Value::Symbol(i) if i == if_ => {
            let mut temp_state = CompileState::new_temp(state, *line);
            let mut end_patches = Vec::new();
            let mut cdr_i = cdr.iter();
            while let Some(r) = cdr_i.next() {
                compile(vm, state, *r, result, line)?;
                if let Some(r) = cdr_i.next() {
                    temp_state.chunk.code.clear();
                    compile(vm, &mut temp_state, *r, result, line)?;
                    temp_state.chunk.encode1(JMPF, 256, *line)?; // Force wide for constant size.
                    state.chunk.encode2(
                        JMPFF,
                        result as u16,
                        temp_state.chunk.code.len() as u16,
                        *line,
                    )?;
                    compile(vm, state, *r, result, line)?;
                    state.chunk.encode1(JMPF, 256, *line)?; // Force wide for constant size.
                    end_patches.push(state.chunk.code.len());
                }
            }
            let end_ip = state.chunk.code.len();
            for i in end_patches {
                let f = (end_ip - i) as u16;
                // XXX TODO, if less then u8 then remove WIDE and pad with NOP
                state.chunk.code[i - 2] = ((f & 0xFF00) >> 8) as u8;
                state.chunk.code[i - 1] = (f & 0x00FF) as u8;
            }
        }
        Value::Symbol(i) if i == do_ => {
            for r in cdr.iter() {
                compile(vm, state, *r, result, line)?;
            }
        }
        Value::Symbol(i) if i == def => {
            if cdr.len() == 2 {
                if let Value::Symbol(si) = cdr[0] {
                    compile(vm, state, cdr[1], result + 1, line)?;
                    let si_const = vm.reserve_index(si);
                    state.chunk.encode_refi(result as u16, si_const, *line)?;
                    state
                        .chunk
                        .encode2(DEF, result as u16, (result + 1) as u16, *line)?;
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
                        compile(vm, state, cdr[1], result, line)?;
                        state
                            .chunk
                            .encode2(SET, (idx + 1) as u16, result as u16, *line)?;
                    } else {
                        compile(vm, state, cdr[1], result + 1, line)?;
                        let si_const = vm.reserve_index(si);
                        state.chunk.encode_refi(result as u16, si_const, *line)?;
                        state
                            .chunk
                            .encode2(DEF, result as u16, (result + 1) as u16, *line)?;
                    }
                } else {
                    return Err(VMError::new_compile("set!: expected symbol"));
                }
            } else {
                return Err(VMError::new_compile("set!: malformed"));
            }
        }
        Value::Symbol(i) if i == inc => {
            let dest = if let Value::Symbol(si) = cdr[0] {
                if let Some(idx) = state.get_symbol(si) {
                    idx + 1
                } else {
                    let const_i = vm.reserve_index(si);
                    state.chunk.encode_refi(result as u16, const_i, *line)?;
                    result
                }
            } else {
                return Err(VMError::new_compile("inc!: expected symbol"));
            };
            if cdr.len() == 1 {
                state.chunk.encode2(INC, dest as u16, 1, *line)?;
            } else if cdr.len() == 2 {
                let amount = match cdr[1] {
                    Value::Byte(i) => i as u16,
                    Value::Int(i) if i >= 0 && i <= u16::MAX as i64 => i as u16,
                    Value::Int(_) => return Err(VMError::new_compile("inc!: second arg to large")),
                    Value::UInt(i) if i <= u16::MAX as u64 => i as u16,
                    Value::UInt(_) => {
                        return Err(VMError::new_compile("inc!: second arg < 0 or to large"))
                    }
                    _ => return Err(VMError::new_compile("inc!: second arg must be integer")),
                };
                state.chunk.encode2(INC, dest as u16, amount, *line)?;
            } else {
                return Err(VMError::new_compile("inc!: malformed"));
            }
        }
        Value::Symbol(i) if i == dec => {
            let dest = if let Value::Symbol(si) = cdr[0] {
                if let Some(idx) = state.get_symbol(si) {
                    idx + 1
                } else {
                    let const_i = vm.reserve_index(si);
                    state.chunk.encode_refi(result as u16, const_i, *line)?;
                    result
                }
            } else {
                return Err(VMError::new_compile("dec!: expected symbol"));
            };
            if cdr.len() == 1 {
                state.chunk.encode2(DEC, dest as u16, 1, *line)?;
            } else if cdr.len() == 2 {
                let amount = match cdr[1] {
                    Value::Byte(i) => i as u16,
                    Value::Int(i) if i >= 0 && i <= u16::MAX as i64 => i as u16,
                    Value::Int(_) => return Err(VMError::new_compile("inc!: second arg to large")),
                    Value::UInt(i) if i <= u16::MAX as u64 => i as u16,
                    Value::UInt(_) => {
                        return Err(VMError::new_compile("inc!: second arg < 0 or to large"))
                    }
                    _ => return Err(VMError::new_compile("inc!: second arg must be integer")),
                };
                state.chunk.encode2(DEC, dest as u16, amount, *line)?;
            } else {
                return Err(VMError::new_compile("dec!: malformed"));
            }
        }
        Value::Symbol(i) if i == add => {
            if cdr.is_empty() {
                compile(vm, state, Value::Int(0), result, line)?;
            } else if cdr.len() == 1 {
                compile(vm, state, cdr[0], result, line)?;
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1, line)?;
                        state.chunk.encode3(
                            ADDM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            *line,
                        )?;
                    } else {
                        compile(vm, state, *v, result, line)?;
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
                    compile(vm, state, Value::Int(-i), result, line)?;
                } else if let Ok(f) = cdr[0].get_float() {
                    compile(vm, state, Value::float(-f), result, line)?;
                }
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1, line)?;
                        state.chunk.encode3(
                            SUBM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            *line,
                        )?;
                    } else {
                        compile(vm, state, *v, result, line)?;
                    }
                }
            }
        }
        Value::Symbol(i) if i == mul => {
            if cdr.is_empty() {
                compile(vm, state, Value::Int(1), result, line)?;
            } else if cdr.len() == 1 {
                compile(vm, state, cdr[0], result, line)?;
            } else {
                for (i, v) in cdr.iter().enumerate() {
                    if i > 0 {
                        compile(vm, state, *v, result + 1, line)?;
                        state.chunk.encode3(
                            MULM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            *line,
                        )?;
                    } else {
                        compile(vm, state, *v, result, line)?;
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
                        compile(vm, state, *v, result + 1, line)?;
                        state.chunk.encode3(
                            DIVM,
                            result as u16,
                            result as u16,
                            (result + 1) as u16,
                            *line,
                        )?;
                    } else {
                        compile(vm, state, *v, result, line)?;
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
        Value::Reference(h) => match vm.get(h) {
            Object::Lambda(_) => compile_call(vm, state, Value::Reference(h), cdr, result, line)?,
            Object::Pair(ncar, ncdr, meta) => {
                if let Some(meta) = meta {
                    *line = meta.line as u32;
                }
                let ncdr: Vec<Value> = ncdr.iter(vm).collect();
                let ncar = *ncar;
                compile_list(vm, state, ncar, &ncdr[..], result, line)?;
                compile_call_reg(vm, state, result as u16, cdr, result, line)?
            }
            Object::Vector(v) => {
                if let Some(ncar) = v.get(0) {
                    let ncar = *ncar;
                    if v.len() > 1 {
                        let ncdr = make_vec_cdr(&v[1..]);
                        compile_list(vm, state, ncar, ncdr, result, line)?;
                    } else {
                        compile_list(vm, state, ncar, &[], result, line)?;
                    }
                    compile_call_reg(vm, state, result as u16, cdr, result, line)?
                }
            }
            _ => {}
        },
        _ => {
            println!("Boo");
        }
    }
    Ok(())
}

fn pass1(vm: &mut Vm, state: &mut CompileState, exp: Value) -> VMResult<()> {
    let fn_ = vm.intern("fn");
    match exp {
        Value::Reference(h) => match vm.get(h).clone() {
            Object::Pair(car, _cdr, _) => {
                // short circuit on an fn form, will be handled with it's own state.
                if let Value::Symbol(i) = car {
                    if i == fn_ {
                        return Ok(());
                    }
                }
                // XXX boo on this collect.
                for r in exp.iter(vm).collect::<Vec<Value>>() {
                    pass1(vm, state, r)?;
                }
            }
            Object::Vector(v) => {
                for r in v {
                    pass1(vm, state, r)?;
                }
            }
            _ => {}
        },
        Value::Symbol(i) => {
            if state.get_symbol(i).is_none() && state.symbols.borrow().can_capture(i) {
                state.symbols.borrow_mut().insert_capture(vm, i);
            }
        }
        Value::True => {}
        Value::False => {}
        Value::Nil => {}
        Value::Undefined => {}
        Value::Byte(_) => {}
        Value::Int(i) if i >= 0 && i <= u16::MAX as i64 => {}
        Value::UInt(i) if i <= u16::MAX as u64 => {}
        _ => {
            state.add_constant(exp);
        }
    }
    Ok(())
}

// Need to break the cdr lifetime away from the vm for a call or we have
// to reallocate stuff for no reason.
// Should be safe because compiling code should not be manupulating values on
// the heap (where the underlying vector lives).
fn make_vec_cdr(cdr: &[Value]) -> &'static [Value] {
    unsafe { &*(cdr as *const [Value]) }
}

fn compile(
    vm: &mut Vm,
    state: &mut CompileState,
    exp: Value,
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    match exp {
        Value::Reference(h) => match vm.get(h) {
            Object::Pair(car, cdr, meta) => {
                if let Some(meta) = meta {
                    *line = meta.line as u32;
                }
                let cdr: Vec<Value> = cdr.iter(vm).collect();
                let car = *car;
                compile_list(vm, state, car, &cdr[..], result, line)?;
            }
            Object::Vector(v) => {
                if let Some(car) = v.get(0) {
                    let car = *car;
                    if v.len() > 1 {
                        let cdr = make_vec_cdr(&v[1..]);
                        compile_list(vm, state, car, cdr, result, line)?;
                    } else {
                        compile_list(vm, state, car, &[], result, line)?;
                    }
                }
            }
            _ => {}
        },
        Value::Symbol(i) => {
            if let Some(idx) = state.get_symbol(i) {
                state
                    .chunk
                    .encode2(MOV, result as u16, (idx + 1) as u16, *line)?;
            } else {
                let const_i = vm.reserve_index(i);
                state.chunk.encode_refi(result as u16, const_i, *line)?;
            }
        }
        Value::True => state.chunk.encode1(MREGT, result as u16, *line)?,
        Value::False => state.chunk.encode1(MREGF, result as u16, *line)?,
        Value::Nil => state.chunk.encode1(MREGN, result as u16, *line)?,
        Value::Undefined => state.chunk.encode1(MREGC, result as u16, *line)?,
        Value::Byte(i) => state.chunk.encode2(MREGB, result as u16, i as u16, *line)?,
        Value::Int(i) if i >= 0 && i <= u16::MAX as i64 => {
            state.chunk.encode2(MREGI, result as u16, i as u16, *line)?
        }
        Value::UInt(i) if i <= u16::MAX as u64 => {
            state.chunk.encode2(MREGU, result as u16, i as u16, *line)?
        }
        _ => {
            let const_i = state.add_constant(exp);
            state
                .chunk
                .encode2(CONST, result as u16, const_i as u16, *line)?;
        }
    }
    Ok(())
}

fn main() {
    let config = if let Some(c) = get_config() {
        c
    } else {
        return;
    };
    let mut vm = Vm::new();
    vm.set_global("pr", Value::Builtin(CallFunc { func: pr }));
    vm.set_global("prn", Value::Builtin(CallFunc { func: prn }));
    let mut reader_state = ReaderState::new();
    //let mut state = CompileState::new();
    let txt = std::fs::read_to_string(&config.script).unwrap();
    let exps = read_all(&mut vm, &mut reader_state, &txt).unwrap();
    let mut line = 1;
    let file_i = vm.intern(&config.script);
    for exp in exps {
        if let Value::Reference(h) = exp {
            if let Object::Pair(_, _, Some(meta)) = vm.get(h) {
                line = meta.line as u32;
            }
        }
        let mut state = CompileState::new_state(vm.get_interned(file_i), line, None);
        pass1(&mut vm, &mut state, exp).unwrap();
        compile(&mut vm, &mut state, exp, 0, &mut line).unwrap();
        state.chunk.encode0(RET, line).unwrap();
        if config.dump {
            state.chunk.disassemble_chunk(&vm, 0).unwrap();
        }
        if config.run {
            let chunk = Rc::new(state.chunk.clone());
            if let Err(err) = vm.execute(chunk) {
                println!("ERROR: {}", err);
                vm.dump_globals();
                //state.chunk.disassemble_chunk(&vm).unwrap();
            }
        }
    }
    //state.chunk.encode0(RET, line).unwrap();
    //println!("Compile: {}", txt);
    if config.globals_pre {
        vm.dump_globals();
    }
    //if config.dump {
    //    state.chunk.disassemble_chunk(&vm, 0).unwrap();
    //}
    /*    if config.run {
        let chunk = Rc::new(state.chunk.clone());
        if let Err(err) = vm.execute(chunk) {
            println!("ERROR: {}", err);
            vm.dump_globals();
            //state.chunk.disassemble_chunk(&vm).unwrap();
        }
    }*/
    if config.globals_post {
        vm.dump_globals();
    }
    //println!("\n\nPOST exec:\n");
    //vm.dump_globals();
    //chunk.disassemble_chunk(&vm).unwrap();
}
