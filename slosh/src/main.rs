extern crate sl_liner;

use std::io::ErrorKind;
use std::sync::Arc;

use slvm::error::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use sl_compiler::compile::*;
use sl_compiler::reader::*;
use sl_compiler::state::*;

use sl_liner::{Context, Prompt};

pub mod debug;
use debug::*;

pub mod print;
use print::*;

fn value_str(vm: &mut Vm, val: Value) -> String {
    pretty_value(vm, val)
}

fn value_dsp_str(vm: &mut Vm, val: Value) -> String {
    display_value(vm, val)
}

fn pr(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    for v in registers {
        print!("{}", value_str(vm, *v));
    }
    Ok(Value::Nil)
}

fn prn(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    for v in registers {
        print!("{}", value_str(vm, *v));
    }
    println!();
    Ok(Value::Nil)
}

fn dasm(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    if registers.len() != 1 {
        return Err(VMError::new_compile(
            "dasm: wrong number of args, expected one",
        ));
    }
    match registers[0].unref(vm) {
        Value::Lambda(handle) => {
            let l = vm.get_lambda(handle);
            l.disassemble_chunk(vm, 0)?;
            Ok(Value::Nil)
        }
        Value::Closure(handle) => {
            let (l, _) = vm.get_closure(handle);
            l.disassemble_chunk(vm, 0)?;
            Ok(Value::Nil)
        }
        _ => Err(VMError::new_vm("DASM: Not a callable.")),
    }
}

fn line_num(line: &Option<&mut u32>) -> u32 {
    match line {
        Some(line) => **line,
        None => 0,
    }
}

fn load(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    if registers.len() != 1 {
        return Err(VMError::new_compile(
            "load: wrong number of args, expected one",
        ));
    }
    let name = match registers[0].unref(vm) {
        Value::StringConst(i) => vm.get_interned(i),
        Value::String(h) => {
            let s = vm.get_string(h);
            let s = s.to_string();
            let s_i = vm.intern(&s);
            vm.get_interned(s_i)
        }
        _ => return Err(VMError::new_vm("load: Not a string.")),
    };
    let txt = std::fs::read_to_string(name).map_err(|e| VMError::new_vm(format!("load: {}", e)))?;
    let mut reader_state = ReaderState::new();
    let exps = read_all(vm, &mut reader_state, &txt)
        .map_err(|e| VMError::new_vm(format!("load: {}", e)))?;
    let mut linenum = 1;
    let mut line = Some(&mut linenum);
    let mut last = Value::Nil;
    for exp in exps {
        if let Value::Pair(h) = exp {
            let (_, _) = vm.get_pair(h);
            if let (Some(line), Some(Value::UInt(dline))) =
                (&mut line, vm.get_heap_property(h, ":dbg-line"))
            {
                **line = dline as u32;
            }
        }
        let mut state = CompileState::new_state(vm, name, line_num(&line), None);
        state.chunk.dbg_args = Some(Vec::new());
        //pass1(vm, &mut state, exp)?;
        //compile(vm, &mut state, exp, 0, &mut line)?;
        //state.chunk.encode0(RET, line)?;
        if let Err(e) = pass1(vm, &mut state, exp) {
            println!("Compile error, {}, line {}: {}", name, line_num(&line), e);
            return Err(e);
        }
        if let Err(e) = compile(vm, &mut state, exp, 0, &mut line) {
            println!("Compile error, {} line {}: {}", name, line_num(&line), e);
            return Err(e);
        }
        if let Err(e) = state.chunk.encode0(RET, Some(line_num(&line))) {
            println!("Compile error, {} line {}: {}", name, line_num(&line), e);
            return Err(e);
        }
        state.chunk.extra_regs = state.max_regs;
        let chunk = Arc::new(state.chunk.clone());
        vm.execute(chunk)?;
        /*            if let Err(err) = vm.execute(chunk) {
            println!("ERROR: {}", err.display(&vm));
            if let Some(err_frame) = vm.err_frame() {
                let ip = err_frame.current_ip;
                let line = err_frame.chunk.offset_to_line(ip).unwrap_or(0);
                println!(
                    "{} line: {} ip: {:#010x}",
                    err_frame.chunk.file_name, line, ip
                );
            }
            debug(vm);
            return Err(err);
        }*/
        last = vm.get_stack(0);
    }
    Ok(last)
}

fn vec_slice(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    let (vector, start, end) = match registers.len() {
        2 => {
            if let (Value::Vector(vector), Ok(start)) = (registers[0], registers[1].get_int()) {
                let v = vm.get_vector(vector);
                (v, start as usize, v.len())
            } else {
                return Err(VMError::new_vm("vec-slice: Invalid arguments".to_string()));
            }
        }
        3 => {
            if let (Value::Vector(vector), Ok(start), Ok(end)) = (registers[0], registers[1].get_int(), registers[2].get_int()) {
                let v = vm.get_vector(vector);
                (v, start as usize, end as usize)
            } else {
                return Err(VMError::new_vm("vec-slice: Invalid arguments".to_string()));
            }
        }
        _ => return Err(VMError::new_vm("vec-slice: Invalid arguments (requires two or three)".to_string())),
    };
    let len = vector.len();
    if start == len && end <= len {
        Ok(vm.alloc_vector(Vec::new()))
    } else if start >= len || end > len {
        Err(VMError::new_vm("vec-slice: Invalid arguments- out of bounds".to_string()))
    } else {
        let new_vec = vector[start..end].to_vec();
        Ok(vm.alloc_vector(new_vec))
    }
}

fn vec_to_list(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    if registers.len() != 1 {
        return Err(VMError::new_vm("vec->list: Invalid arguments (requires one vector)".to_string()));
    }
    if let Value::Vector(vhandle) = registers[0] {
        let vector = vm.get_vector(vhandle).to_vec();

        let mut last = Value::Nil;
        for item in vector
            .iter()
            .rev()
        {
            let old_last = last;
            last = vm.alloc_pair(*item, old_last);
        }
        Ok(last)
    } else {
        Err(VMError::new_vm("vec->list: Invalid arguments (requires one vector)".to_string()))
    }

}

const PROMPT_FN: &str = "prompt";
fn main() {
    let mut con = Context::new();

    if let Err(e) = con.history.set_file_name_and_load_history("history") {
        println!("Error loading history: {}", e);
    }
    let mut vm = Vm::new();
    vm.set_global("pr", Value::Builtin(CallFunc { func: pr }));
    vm.set_global("prn", Value::Builtin(CallFunc { func: prn }));
    vm.set_global("dasm", Value::Builtin(CallFunc { func: dasm }));
    vm.set_global("load", Value::Builtin(CallFunc { func: load }));
    vm.set_global("vec-slice", Value::Builtin(CallFunc { func: vec_slice }));
    vm.set_global("vec->list", Value::Builtin(CallFunc { func: vec_to_list }));
    //vm.set_global("eval", Value::Builtin(CallFunc { func: eval }));
    loop {
        let res = match con.read_line(Prompt::from("slosh> "), None) {
            Ok(input) => input,
            Err(err) => match err.kind() {
                ErrorKind::UnexpectedEof => {
                    break;
                }
                ErrorKind::Interrupted => {
                    continue;
                }
                _ => {
                    eprintln!("Error on input: {}", err);
                    continue;
                }
            },
        };

        if res.is_empty() {
            continue;
        }

        con.history.push(&res).expect("Failed to push history.");
        let mut reader_state = ReaderState::new();
        let exps = read_all(&mut vm, &mut reader_state, &res);
        match exps {
            Ok(exps) => {
                let mut linenum = 1;
                let mut line = Some(&mut linenum);
                for exp in exps {
                    /*if let Value::Pair(h) = exp {
                        let (_, _) = vm.get_pair(h);
                        if let Some(Value::UInt(dline)) = vm.get_heap_property(h, ":dbg-line") {
                            line = dline as u32;
                        }
                    }*/
                    let mut state =
                        CompileState::new_state(&mut vm, PROMPT_FN, line_num(&line), None);
                    if let Err(e) = pass1(&mut vm, &mut state, exp) {
                        println!("Compile error, line {}: {}", line_num(&line), e);
                    }
                    if let Err(e) = compile(&mut vm, &mut state, exp, 0, &mut line) {
                        println!("Compile error, line {}: {}", line_num(&line), e);
                    }
                    if let Err(e) = state.chunk.encode0(RET, Some(line_num(&line))) {
                        println!("Compile error, line {}: {}", line_num(&line), e);
                    }
                    let chunk = Arc::new(state.chunk.clone());
                    if let Err(err) = vm.execute(chunk) {
                        println!("ERROR: {}", err.display(&vm));
                        if let Some(err_frame) = vm.err_frame() {
                            let ip = err_frame.current_ip;
                            let line = err_frame.chunk.offset_to_line(ip).unwrap_or(0);
                            println!(
                                "{} line: {} ip: {:#010x}",
                                err_frame.chunk.file_name, line, ip
                            );
                        }
                        debug(&mut vm);
                    } else {
                        //println!("{}", vm.get_stack(0).display_value(&vm));
                        let reg = vm.get_stack(0);
                        println!("{}", value_dsp_str(&mut vm, reg));
                    }
                }
            }
            Err(err) => println!("Reader error: {}", err),
        }
    }
}
