use std::rc::Rc;

use slvm::error::*;
use slvm::heap::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use crate::backquote::*;
use crate::state::*;

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
    let tail = state.tail;
    state.tail = false;
    let result = if tail { 0 } else { result };
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    state
        .chunk
        .encode2(CONST, b_reg as u16, const_i as u16, *line)?;
    if tail {
        state
            .chunk
            .encode2(TCALL, b_reg as u16, cdr.len() as u16, *line)?;
    } else {
        state
            .chunk
            .encode3(CALL, b_reg as u16, cdr.len() as u16, result as u16, *line)?;
    }
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
    let tail = state.tail;
    state.tail = false;
    let result = if tail { 0 } else { result };
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    if tail {
        state.chunk.encode_tcallg(global, cdr.len() as u16, *line)?;
    } else {
        state
            .chunk
            .encode_callg(global, cdr.len() as u16, result as u16, *line)?;
    }
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
    let tail = state.tail;
    state.tail = false;
    let result = if tail { 0 } else { result };
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    if tail {
        state.chunk.encode2(TCALL, reg, cdr.len() as u16, *line)?;
    } else {
        state
            .chunk
            .encode3(CALL, reg, cdr.len() as u16, result as u16, *line)?;
    }
    Ok(())
}

fn compile_call_myself(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let tail = state.tail;
    state.tail = false;
    let result = if tail { 0 } else { result };
    for (i, r) in cdr.iter().enumerate() {
        compile(vm, state, *r, result + i + 1, line)?;
    }
    if tail {
        state.chunk.encode1(TCALLM, cdr.len() as u16, *line)?;
    } else {
        state
            .chunk
            .encode2(CALLM, cdr.len() as u16, result as u16, *line)?;
    }
    Ok(())
}

fn new_state(
    vm: &mut Vm,
    state: &mut CompileState,
    args: Value,
    line: &mut u32,
) -> VMResult<CompileState> {
    match args {
        Value::Reference(h) => {
            let new_state = CompileState::new_state(
                vm,
                state.chunk.file_name,
                *line,
                Some(state.symbols.clone()),
            );
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
            for a in args_iter {
                if let Value::Symbol(i) = a {
                    new_state.symbols.borrow_mut().data.borrow_mut().add_sym(i);
                } else {
                    return Err(VMError::new_compile(
                        "Malformed fn, invalid args, must be symbols.",
                    ));
                }
            }
            Ok(new_state)
        }
        Value::Nil => Ok(CompileState::new_state(
            vm,
            state.chunk.file_name,
            *line,
            Some(state.symbols.clone()),
        )),
        _ => {
            return Err(VMError::new_compile(format!(
                "Malformed fn, invalid args, {:?}.",
                args
            )))
        }
    }
}

fn compile_fn(
    vm: &mut Vm,
    state: &mut CompileState,
    args: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let mut new_state = new_state(vm, state, args, line)?;
    for r in cdr.iter() {
        pass1(vm, &mut new_state, *r).unwrap();
    }
    let reserved = new_state.reserved_regs();
    let last_thing = cdr.len() - 1;
    for (i, r) in cdr.iter().enumerate() {
        if i == last_thing {
            new_state.tail = true;
        }
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
    new_state.chunk.input_regs = reserved;
    new_state.chunk.extra_regs = new_state.max_regs - reserved;
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

fn compile_macro(
    vm: &mut Vm,
    state: &mut CompileState,
    args: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let mut new_state = new_state(vm, state, args, line)?;
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
    let mac = Value::Reference(vm.alloc(Object::Macro(Rc::new(new_state.chunk))));
    let const_i = state.add_constant(mac);
    state
        .chunk
        .encode2(CONST, result as u16, const_i as u16, *line)?;
    Ok(())
}

fn make_math_comp(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
    op: u8,
) -> VMResult<()> {
    if cdr.len() <= 1 {
        return Err(VMError::new_compile("Requires at least two arguments."));
    } else {
        let mut max = 0;
        for (i, v) in cdr.iter().enumerate() {
            max = result + i + 1;
            compile(vm, state, *v, max, line)?;
        }
        state
            .chunk
            .encode3(op, result as u16, (result + 1) as u16, max as u16, *line)?;
    }
    Ok(())
}
fn compile_math(
    vm: &mut Vm,
    state: &mut CompileState,
    car: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<bool> {
    match car {
        Value::Symbol(i) if i == state.specials.inc => {
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
        Value::Symbol(i) if i == state.specials.dec => {
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
        Value::Symbol(i) if i == state.specials.add => {
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
        Value::Symbol(i) if i == state.specials.sub => {
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
        Value::Symbol(i) if i == state.specials.mul => {
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
        Value::Symbol(i) if i == state.specials.div => {
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
        Value::Symbol(i) if i == state.specials.numeq => {
            make_math_comp(vm, state, cdr, result, line, NUMEQ)?;
        }
        Value::Symbol(i) if i == state.specials.numneq => {
            make_math_comp(vm, state, cdr, result, line, NUMNEQ)?;
        }
        Value::Symbol(i) if i == state.specials.numlt => {
            make_math_comp(vm, state, cdr, result, line, NUMLT)?;
        }
        Value::Symbol(i) if i == state.specials.numlte => {
            make_math_comp(vm, state, cdr, result, line, NUMLTE)?;
        }
        Value::Symbol(i) if i == state.specials.numgt => {
            make_math_comp(vm, state, cdr, result, line, NUMGT)?;
        }
        Value::Symbol(i) if i == state.specials.numgte => {
            make_math_comp(vm, state, cdr, result, line, NUMGTE)?;
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn compile_if(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    let mut temp_state = CompileState::new_temp(vm, state, *line);
    let tail = state.tail;
    state.tail = false;
    let mut end_patches = Vec::new();
    let mut cdr_i = cdr.iter();
    while let Some(r) = cdr_i.next() {
        compile(vm, state, *r, result, line)?;
        if let Some(r) = cdr_i.next() {
            state.tail = tail;
            temp_state.tail = tail;
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
            state.tail = false;
        }
    }
    let end_ip = state.chunk.code.len();
    for i in end_patches {
        let f = (end_ip - i) as u16;
        // XXX TODO, if less then u8 then remove WIDE and pad with NOP
        state.chunk.code[i - 2] = ((f & 0xFF00) >> 8) as u8;
        state.chunk.code[i - 1] = (f & 0x00FF) as u8;
    }
    Ok(())
}

fn compile_def(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
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
    Ok(())
}

fn compile_set(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
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
    if !compile_math(vm, state, car, cdr, result, line)? {
        match car {
            Value::Symbol(i) if i == state.specials.fn_ => {
                if cdr.len() > 1 {
                    compile_fn(vm, state, cdr[0], &cdr[1..], result, line)?
                } else {
                    return Err(VMError::new_compile("Malformed fn form."));
                }
            }
            Value::Symbol(i) if i == state.specials.mac_ => {
                if cdr.len() > 1 {
                    compile_macro(vm, state, cdr[0], &cdr[1..], result, line)?
                } else {
                    return Err(VMError::new_compile("Malformed macro form."));
                }
            }
            Value::Symbol(i) if i == state.specials.if_ => {
                compile_if(vm, state, cdr, result, line)?;
            }
            Value::Symbol(i) if i == state.specials.do_ => {
                let last_thing = cdr.len() - 1;
                let old_tail = state.tail;
                state.tail = false;
                for (i, r) in cdr.iter().enumerate() {
                    if i == last_thing {
                        state.tail = old_tail;
                    }
                    compile(vm, state, *r, result, line)?;
                }
            }
            Value::Symbol(i) if i == state.specials.def => {
                state.tail = false;
                compile_def(vm, state, cdr, result, line)?;
            }
            Value::Symbol(i) if i == state.specials.set => {
                state.tail = false;
                compile_set(vm, state, cdr, result, line)?;
            }
            Value::Symbol(i) if i == state.specials.list => {
                state.tail = false;
                let mut max = 0;
                for r in cdr {
                    compile(vm, state, *r, result + max + 1, line)?;
                    max += 1;
                }
                state.chunk.encode3(
                    LIST,
                    result as u16,
                    (result + 1) as u16,
                    (result + max + 1) as u16,
                    *line,
                )?;
            }
            Value::Symbol(i) if i == state.specials.list_append => {
                state.tail = false;
                let mut max = 0;
                for r in cdr {
                    compile(vm, state, *r, result + max + 1, line)?;
                    max += 1;
                }
                state.chunk.encode3(
                    APND,
                    result as u16,
                    (result + 1) as u16,
                    (result + max + 1) as u16,
                    *line,
                )?;
            }
            Value::Symbol(i) if i == state.specials.quote => {
                state.tail = false;
                if cdr.len() != 1 {
                    return Err(VMError::new_compile(format!(
                        "quote takes one argument, got {}, line {}",
                        cdr.len(),
                        line
                    )));
                }
                mkconst(vm, state, cdr[0], result, line)?;
            }
            Value::Symbol(i) if i == state.specials.backquote => {
                state.tail = false;
                if cdr.len() != 1 {
                    return Err(VMError::new_compile(format!(
                        "backquote takes one argument, got {}, line {}",
                        cdr.len(),
                        line
                    )));
                }
                backquote(vm, state, cdr[0], result, line)?;
            }
            Value::Symbol(i) if i == state.specials.recur => {
                if !state.tail {
                    return Err(VMError::new_compile(format!(
                        "recur not in tail position, line {}",
                        line
                    )));
                }
                compile_call_myself(vm, state, cdr, result, line)?
            }
            Value::Symbol(i) if i == state.specials.this_fn => {
                compile_call_myself(vm, state, cdr, result, line)?
            }
            Value::Symbol(i) if i == state.specials.eq => {
                if cdr.len() <= 1 {
                    return Err(VMError::new_compile("Requires at least two arguments."));
                } else {
                    let mut max = 0;
                    for (i, v) in cdr.iter().enumerate() {
                        compile(vm, state, *v, result + i + 1, line)?;
                        max = result + i + 1;
                    }
                    state.chunk.encode3(
                        EQ,
                        result as u16,
                        (result + 1) as u16,
                        max as u16,
                        *line,
                    )?;
                }
            }
            Value::Symbol(i) if i == state.specials.eqv => {
                if cdr.len() <= 1 {
                    return Err(VMError::new_compile("Requires at least two arguments."));
                } else {
                    let mut max = 0;
                    for (i, v) in cdr.iter().enumerate() {
                        compile(vm, state, *v, result + i + 1, line)?;
                        max = result + i + 1;
                    }
                    state.chunk.encode3(
                        EQV,
                        result as u16,
                        (result + 1) as u16,
                        max as u16,
                        *line,
                    )?;
                }
            }
            Value::Symbol(i) if i == state.specials.equal => {
                if cdr.len() <= 1 {
                    return Err(VMError::new_compile("Requires at least two arguments."));
                } else {
                    let mut max = 0;
                    for (i, v) in cdr.iter().enumerate() {
                        compile(vm, state, *v, result + i + 1, line)?;
                        max = result + i + 1;
                    }
                    state.chunk.encode3(
                        EQUAL,
                        result as u16,
                        (result + 1) as u16,
                        max as u16,
                        *line,
                    )?;
                }
            }
            Value::Symbol(i) => {
                if let Some(idx) = state.get_symbol(i) {
                    compile_call_reg(vm, state, (idx + 1) as u16, cdr, result, line)?
                } else {
                    let slot = vm.reserve_index(i);
                    // Is a global so set up a call and will error at runtime if
                    // not callable (dynamic is fun).
                    let global = vm.get_global(slot);
                    if let Value::Undefined = global {
                        eprintln!("Warning: {} not defined.", vm.get_interned(i));
                    }
                    let mut mac = None;
                    if let Value::Reference(h) = global {
                        if let Object::Macro(chunk) = vm.get(h) {
                            mac = Some(chunk.clone());
                        }
                    }
                    if let Some(mac) = mac {
                        let exp = vm.do_call(mac, cdr)?;
                        //println!("XXX expanded  {}", exp.display_value(vm));
                        pass1(vm, state, exp)?;
                        compile(vm, state, exp, result, line)?
                    } else {
                        compile_callg(vm, state, slot as u32, cdr, result, line)?
                    }
                }
            }
            Value::Builtin(builtin) => {
                compile_call(vm, state, Value::Builtin(builtin), cdr, result, line)?
            }
            Value::Reference(h) => match vm.get(h) {
                Object::Lambda(_) => {
                    compile_call(vm, state, Value::Reference(h), cdr, result, line)?
                }
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
                println!("Boo, {}", car.display_value(vm));
            }
        }
    }
    Ok(())
}

pub fn pass1(vm: &mut Vm, state: &mut CompileState, exp: Value) -> VMResult<()> {
    let fn_ = vm.intern("fn");
    let mac_ = vm.intern("macro");
    match exp {
        Value::Reference(h) => match vm.get(h).clone() {
            Object::Pair(car, _cdr, _) => {
                // short circuit on an fn form, will be handled with it's own state.
                if let Value::Symbol(i) = car {
                    if i == fn_ || i == mac_ {
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

pub fn mkconst(
    _vm: &mut Vm,
    state: &mut CompileState,
    exp: Value,
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    match exp {
        Value::True => state.chunk.encode1(MREGT, result as u16, *line)?,
        Value::False => state.chunk.encode1(MREGF, result as u16, *line)?,
        Value::Nil => state.chunk.encode1(MREGN, result as u16, *line)?,
        Value::Undefined => state.chunk.encode1(MREGC, result as u16, *line)?,
        Value::Byte(i) => state.chunk.encode2(MREGB, result as u16, i as u16, *line)?,
        Value::Int(i) if i >= 0 && i <= u16::MAX as i64 => {
            state.chunk.encode2(MREGI, result as u16, i as u16, *line)?;
        }
        Value::UInt(i) if i <= u16::MAX as u64 => {
            state.chunk.encode2(MREGU, result as u16, i as u16, *line)?;
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

pub fn compile(
    vm: &mut Vm,
    state: &mut CompileState,
    exp: Value,
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    if state.max_regs < result {
        state.max_regs = result;
    }
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
