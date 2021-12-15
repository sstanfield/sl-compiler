use std::collections::HashMap;
use std::rc::Rc;

use slvm::error::*;
use slvm::heap::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use crate::backquote::*;
use crate::state::*;

fn compile_params(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    tail: bool,
    line: &mut u32,
) -> VMResult<()> {
    fn move_locals(
        state: &mut CompileState,
        var_map: &HashMap<usize, Vec<usize>>,
        var_skips: &mut Vec<usize>,
        idx: usize,
        line: &mut u32,
    ) -> VMResult<()> {
        if let Some(t_vec) = var_map.get(&idx) {
            for target in t_vec {
                if *target > idx {
                    move_locals(state, var_map, var_skips, *target, line)?;
                    var_skips.push(*target);
                    state
                        .chunk
                        .encode2(MOV, *target as u16, idx as u16, *line)?;
                }
            }
        }
        Ok(())
    }
    if tail {
        let mut var_map: HashMap<usize, Vec<usize>> = HashMap::new();
        let mut var_skips = Vec::new();
        for (i, r) in cdr.iter().enumerate() {
            if let Value::Symbol(intern) = r {
                if let Some(idx) = state.get_symbol(*intern) {
                    if i != idx {
                        if let Some(v) = var_map.get_mut(&(idx + 1)) {
                            v.push(i + 1);
                        } else {
                            var_map.insert(idx + 1, vec![i + 1]);
                        }
                    }
                }
            }
        }
        for (i, r) in cdr.iter().enumerate() {
            if !var_skips.contains(&(i + 1)) {
                move_locals(state, &var_map, &mut var_skips, i + 1, line)?;
                compile(vm, state, *r, i + 1, line)?;
            }
        }
    } else {
        for (i, r) in cdr.iter().enumerate() {
            compile(vm, state, *r, result + i + 1, line)?;
        }
    }
    Ok(())
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
    let tail = state.tail;
    state.tail = false;
    compile_params(vm, state, cdr, result, tail, line)?;
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
    compile_params(vm, state, cdr, result, tail, line)?;
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
    compile_params(vm, state, cdr, result, tail, line)?;
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
    compile_params(vm, state, cdr, result, tail, line)?;
    if tail {
        state.chunk.encode1(TCALLM, cdr.len() as u16, *line)?;
    } else {
        state
            .chunk
            .encode2(CALLM, cdr.len() as u16, result as u16, *line)?;
    }
    Ok(())
}

fn mk_state(
    vm: &mut Vm,
    state: &mut CompileState,
    args: Value,
    line: &mut u32,
) -> VMResult<(CompileState, Option<Vec<Value>>)> {
    fn get_args_iter<'vm>(
        vm: &'vm Vm,
        args: Value,
        obj: &Object,
        line: &mut u32,
    ) -> VMResult<Box<dyn Iterator<Item = Value> + 'vm>> {
        match obj {
            Object::Pair(_car, _cdr, meta) => {
                if let Some(meta) = meta {
                    *line = meta.line as u32;
                }
                Ok(args.iter(vm))
            }
            Object::Vector(_v) => Ok(args.iter(vm)),
            _ => {
                return Err(VMError::new_compile(format!(
                    "Malformed fn, invalid args, {:?}.",
                    obj
                )));
            }
        }
    }
    match args {
        Value::Reference(h) => {
            let mut new_state = CompileState::new_state(
                vm,
                state.chunk.file_name,
                *line,
                Some(state.symbols.clone()),
            );
            let obj = vm.get(h);
            let args_iter = get_args_iter(vm, args, obj, line)?;
            let mut opt = false;
            let mut rest = false;
            let mut opt_comps = Vec::new();
            new_state.chunk.dbg_args = Some(Vec::new());
            for a in args_iter {
                match a {
                    Value::Symbol(i) => {
                        if i == new_state.specials.rest {
                            rest = true;
                        } else {
                            new_state.symbols.borrow_mut().data.borrow_mut().add_sym(i);
                            if let Some(dbg_args) = state.chunk.dbg_args.as_mut() {
                                dbg_args.push(i);
                            }
                            if opt {
                                new_state.chunk.opt_args += 1;
                            } else {
                                new_state.chunk.args += 1;
                            }
                        }
                    }
                    Value::Reference(h) => {
                        let obj = vm.get(h);
                        let mut args_iter = get_args_iter(vm, a, obj, line)?;
                        opt = true;
                        if let Some(Value::Symbol(i)) = args_iter.next() {
                            new_state.symbols.borrow_mut().data.borrow_mut().add_sym(i);
                            if let Some(dbg_args) = state.chunk.dbg_args.as_mut() {
                                dbg_args.push(i);
                            }
                            new_state.chunk.opt_args += 1;
                            if let Some(r) = args_iter.next() {
                                opt_comps.push(r);
                            }
                            // XXX Check to make sure only two elements...
                        }
                    }
                    _ => {
                        return Err(VMError::new_compile(
                            "Malformed fn, invalid args, must be symbols.",
                        ))
                    }
                }
            }
            new_state.chunk.rest = rest;
            if !opt_comps.is_empty() {
                Ok((new_state, Some(opt_comps)))
            } else {
                Ok((new_state, None))
            }
        }
        Value::Nil => Ok((
            CompileState::new_state(
                vm,
                state.chunk.file_name,
                *line,
                Some(state.symbols.clone()),
            ),
            None,
        )),
        _ => Err(VMError::new_compile(format!(
            "Malformed fn, invalid args, {:?}.",
            args
        ))),
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
    let (mut new_state, opt_comps) = mk_state(vm, state, args, line)?;
    for r in cdr.iter() {
        pass1(vm, &mut new_state, *r).unwrap();
    }
    let reserved = new_state.reserved_regs();
    if let Some(opt_comps) = opt_comps {
        let mut temp_state = CompileState::new_temp(vm, &new_state, *line);
        for (i, r) in opt_comps.into_iter().enumerate() {
            let target_reg = new_state.chunk.args as usize + i + 1;
            temp_state.chunk.code.clear();
            let mut tline = *line;
            compile(vm, &mut temp_state, r, reserved, &mut tline)?;
            temp_state
                .chunk
                .encode2(MOV, target_reg as u16, reserved as u16, *line)?;
            new_state.chunk.encode2(
                JMPFNU,
                target_reg as u16,
                temp_state.chunk.code.len() as u16,
                *line,
            )?;
            compile(vm, &mut new_state, r, reserved, line)?;
            new_state
                .chunk
                .encode2(MOV, target_reg as u16, reserved as u16, *line)?;
        }
    }
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
    let (mut new_state, opt_comps) = mk_state(vm, state, args, line)?;
    for r in cdr.iter() {
        pass1(vm, &mut new_state, *r).unwrap();
    }
    let reserved = new_state.reserved_regs();
    if let Some(opt_comps) = opt_comps {
        let mut temp_state = CompileState::new_temp(vm, &new_state, *line);
        for (i, r) in opt_comps.into_iter().enumerate() {
            let target_reg = new_state.chunk.args as usize + i + 1;
            temp_state.chunk.code.clear();
            let mut tline = *line;
            compile(vm, &mut temp_state, r, reserved, &mut tline)?;
            temp_state
                .chunk
                .encode2(MOV, target_reg as u16, reserved as u16, *line)?;
            new_state.chunk.encode2(
                JMPFNU,
                target_reg as u16,
                temp_state.chunk.code.len() as u16,
                *line,
            )?;
            compile(vm, &mut new_state, r, reserved, line)?;
            new_state
                .chunk
                .encode2(MOV, target_reg as u16, reserved as u16, *line)?;
        }
    }
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

fn compile_cons(
    vm: &mut Vm,
    state: &mut CompileState,
    car: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<bool> {
    match car {
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
        Value::Symbol(i) if i == state.specials.cons => {
            state.tail = false;
            if cdr.len() != 2 {
                return Err(VMError::new_compile(format!(
                    "takes two arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result + 1, line)?;
            compile(vm, state, cdr[1], result + 2, line)?;
            state.chunk.encode3(
                CONS,
                result as u16,
                (result + 1) as u16,
                (result + 2) as u16,
                *line,
            )?;
        }
        Value::Symbol(i) if i == state.specials.car => {
            state.tail = false;
            if cdr.len() != 1 {
                return Err(VMError::new_compile(format!(
                    "takes one argument, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result + 1, line)?;
            state
                .chunk
                .encode2(CAR, result as u16, (result + 1) as u16, *line)?;
        }
        Value::Symbol(i) if i == state.specials.cdr => {
            state.tail = false;
            if cdr.len() != 1 {
                return Err(VMError::new_compile(format!(
                    "takes one argument, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result + 1, line)?;
            state
                .chunk
                .encode2(CDR, result as u16, (result + 1) as u16, *line)?;
        }
        Value::Symbol(i) if i == state.specials.xar => {
            state.tail = false;
            if cdr.len() != 2 {
                return Err(VMError::new_compile(format!(
                    "takes two arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result, line)?;
            compile(vm, state, cdr[1], result + 1, line)?;
            state
                .chunk
                .encode2(XAR, result as u16, (result + 1) as u16, *line)?;
        }
        Value::Symbol(i) if i == state.specials.xdr => {
            state.tail = false;
            if cdr.len() != 2 {
                return Err(VMError::new_compile(format!(
                    "takes two arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result, line)?;
            compile(vm, state, cdr[1], result + 1, line)?;
            state
                .chunk
                .encode2(XDR, result as u16, (result + 1) as u16, *line)?;
        }
        _ => return Ok(false),
    }
    Ok(true)
}

fn compile_vec(
    vm: &mut Vm,
    state: &mut CompileState,
    car: Value,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<bool> {
    match car {
        Value::Symbol(i) if i == state.specials.vec => {
            state.tail = false;
            let mut max = 0;
            for r in cdr {
                compile(vm, state, *r, result + max + 1, line)?;
                max += 1;
            }
            state.chunk.encode3(
                VEC,
                result as u16,
                (result + 1) as u16,
                (result + max + 1) as u16,
                *line,
            )?;
        }
        Value::Symbol(i) if i == state.specials.make_vec => {
            state.tail = false;
            if cdr.is_empty() {
                state
                    .chunk
                    .encode3(VEC, result as u16, result as u16, result as u16, *line)?;
            } else if cdr.len() == 1 {
                compile(vm, state, cdr[0], result + 1, line)?;
                state
                    .chunk
                    .encode2(VECMK, result as u16, (result + 1) as u16, *line)?;
            } else if cdr.len() == 2 {
                compile(vm, state, cdr[0], result + 1, line)?;
                compile(vm, state, cdr[1], result + 2, line)?;
                state.chunk.encode3(
                    VECMKD,
                    result as u16,
                    (result + 1) as u16,
                    (result + 2) as u16,
                    *line,
                )?;
            } else {
                return Err(VMError::new_compile(format!(
                    "takes up to two arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
        }
        Value::Symbol(i) if i == state.specials.vec_push => {
            state.tail = false;
            if cdr.len() != 2 {
                return Err(VMError::new_compile(format!(
                    "takes two arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result, line)?;
            compile(vm, state, cdr[1], result + 1, line)?;
            state
                .chunk
                .encode2(VECPSH, result as u16, (result + 1) as u16, *line)?;
        }
        Value::Symbol(i) if i == state.specials.vec_pop => {
            state.tail = false;
            if cdr.len() != 1 {
                return Err(VMError::new_compile(format!(
                    "takes one argument, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result + 1, line)?;
            state
                .chunk
                .encode2(VECPOP, (result + 1) as u16, result as u16, *line)?;
        }
        Value::Symbol(i) if i == state.specials.vec_nth => {
            state.tail = false;
            if cdr.len() != 2 {
                return Err(VMError::new_compile(format!(
                    "takes two arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result + 1, line)?;
            compile(vm, state, cdr[1], result + 2, line)?;
            state.chunk.encode3(
                VECNTH,
                (result + 1) as u16,
                result as u16,
                (result + 2) as u16,
                *line,
            )?;
        }
        Value::Symbol(i) if i == state.specials.vec_set => {
            state.tail = false;
            if cdr.len() != 3 {
                return Err(VMError::new_compile(format!(
                    "takes three arguments, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result, line)?;
            compile(vm, state, cdr[1], result + 1, line)?;
            compile(vm, state, cdr[2], result + 2, line)?;
            state.chunk.encode3(
                VECSTH,
                result as u16,
                (result + 2) as u16,
                (result + 1) as u16,
                *line,
            )?;
        }
        Value::Symbol(i) if i == state.specials.vec_len => {
            state.tail = false;
            if cdr.len() != 1 {
                return Err(VMError::new_compile(format!(
                    "takes one argument, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result + 1, line)?;
            state
                .chunk
                .encode2(VECLEN, result as u16, (result + 1) as u16, *line)?;
        }
        Value::Symbol(i) if i == state.specials.vec_clr => {
            state.tail = false;
            if cdr.len() != 1 {
                return Err(VMError::new_compile(format!(
                    "takes one argument, got {}, line {}",
                    cdr.len(),
                    line
                )));
            }
            compile(vm, state, cdr[0], result, line)?;
            state.chunk.encode1(VECCLR, result as u16, *line)?;
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
    if cdr.is_empty() {
        return Err(VMError::new_compile(format!(
            "requires at least one argument, got 0, line {}",
            line
        )));
    }
    let mut temp_state = CompileState::new_temp(vm, state, *line);
    let tail = state.tail;
    state.tail = false;
    let mut end_patches = Vec::new();
    let mut cdr_i = cdr.iter();
    while let Some(r) = cdr_i.next() {
        let next = cdr_i.next();
        if next.is_none() {
            state.tail = tail;
        }
        compile(vm, state, *r, result, line)?;
        if let Some(r) = next {
            state.tail = tail;
            temp_state.tail = tail;
            temp_state.chunk.code.clear();
            let mut tline = *line;
            compile(vm, &mut temp_state, *r, result, &mut tline)?;
            temp_state.chunk.encode1(JMPF, 256, tline)?; // Force wide for constant size.
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
        state.tail = false;
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

fn compile_and(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    if cdr.is_empty() {
        return Err(VMError::new_compile(format!(
            "requires at least one argument, got 0, line {}",
            line
        )));
    }
    let tail = state.tail;
    state.tail = false;
    let mut end_patches = Vec::new();
    let mut cdr_i = cdr.iter();
    let mut next = cdr_i.next();
    while let Some(r) = next {
        next = cdr_i.next();
        if next.is_none() {
            state.tail = tail;
        }
        compile(vm, state, *r, result, line)?;
        state.chunk.encode2(JMPFF, result as u16, 256, *line)?; // Force wide for constant size.
        end_patches.push(state.chunk.code.len());
        state.tail = false;
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

fn compile_or(
    vm: &mut Vm,
    state: &mut CompileState,
    cdr: &[Value],
    result: usize,
    line: &mut u32,
) -> VMResult<()> {
    if cdr.is_empty() {
        return Err(VMError::new_compile(format!(
            "requires at least one argument, got 0, line {}",
            line
        )));
    }
    let tail = state.tail;
    state.tail = false;
    let mut end_patches = Vec::new();
    let mut cdr_i = cdr.iter();
    let mut next = cdr_i.next();
    while let Some(r) = next {
        next = cdr_i.next();
        if next.is_none() {
            state.tail = tail;
        }
        compile(vm, state, *r, result, line)?;
        state.chunk.encode2(JMPFT, result as u16, 256, *line)?; // Force wide for constant size.
        end_patches.push(state.chunk.code.len());
        state.tail = false;
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
    } else if cdr.len() == 3 {
        // XXX implement docstrings
        if let Value::Symbol(si) = cdr[0] {
            compile(vm, state, cdr[2], result + 1, line)?;
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
    if !(compile_math(vm, state, car, cdr, result, line)?
        || compile_cons(vm, state, car, cdr, result, line)?
        || compile_vec(vm, state, car, cdr, result, line)?)
    {
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
            Value::Symbol(i) if i == state.specials.equal => {
                if cdr.len() <= 1 {
                    return Err(VMError::new_compile("Requires at least two arguments. 2"));
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
            Value::Symbol(i) if i == state.specials.type_ => {
                if cdr.len() != 1 {
                    return Err(VMError::new_compile("Requires one argument."));
                } else {
                    compile(vm, state, cdr[0], result + 1, line)?;
                    state
                        .chunk
                        .encode2(TYPE, result as u16, (result + 1) as u16, *line)?;
                }
            }
            Value::Symbol(i) if i == state.specials.not => {
                if cdr.len() != 1 {
                    return Err(VMError::new_compile("Requires one argument."));
                } else {
                    compile(vm, state, cdr[0], result + 1, line)?;
                    state
                        .chunk
                        .encode2(NOT, result as u16, (result + 1) as u16, *line)?;
                }
            }
            Value::Symbol(i) if i == state.specials.err => {
                let len = cdr.len();
                if len != 1 && len != 2 {
                    return Err(VMError::new_compile("Requires one or two arguments."));
                } else {
                    if len == 2 {
                        compile(vm, state, cdr[0], result, line)?;
                        compile(vm, state, cdr[1], result + 1, line)?;
                    } else {
                        let error = vm.intern("error");
                        compile(vm, state, Value::Keyword(error), result, line)?;
                        compile(vm, state, cdr[0], result + 1, line)?;
                    }
                    state
                        .chunk
                        .encode2(ERR, result as u16, (result + 1) as u16, *line)?;
                }
            }
            Value::Symbol(i) if i == state.specials.and => {
                compile_and(vm, state, cdr, result, line)?;
            }
            Value::Symbol(i) if i == state.specials.or => {
                compile_or(vm, state, cdr, result, line)?;
            }
            Value::Symbol(i) if i == state.specials.str_ => {
                let mut max = 0;
                for (i, v) in cdr.iter().enumerate() {
                    compile(vm, state, *v, result + i + 1, line)?;
                    max = result + i + 1;
                }
                state
                    .chunk
                    .encode3(STR, result as u16, (result + 1) as u16, max as u16, *line)?;
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
                if let Some(dbg_args) = state.chunk.dbg_args.as_mut() {
                    dbg_args.push(i);
                }
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
                if result != idx + 1 {
                    state
                        .chunk
                        .encode2(MOV, result as u16, (idx + 1) as u16, *line)?;
                }
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
