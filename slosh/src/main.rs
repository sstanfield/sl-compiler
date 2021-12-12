extern crate sl_liner;

use std::io::ErrorKind;
use std::rc::Rc;

use slvm::error::*;
use slvm::heap::*;
use slvm::opcodes::*;
use slvm::value::*;
use slvm::vm::*;

use sl_compiler::compile::*;
use sl_compiler::reader::*;
use sl_compiler::state::*;

use sl_liner::{Context, Prompt};

pub mod debug;
use debug::*;

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

fn dasm(vm: &mut Vm, registers: &[Value]) -> VMResult<Value> {
    if registers.len() != 1 {
        return Err(VMError::new_compile(
            "dasm: wrong number of args, expected one",
        ));
    }
    match registers[0].unref(vm) {
        Value::Reference(h) => match vm.get(h) {
            Object::Lambda(l) => {
                l.disassemble_chunk(vm, 0).unwrap();
                Ok(Value::Nil)
            }
            Object::Closure(l, _caps) => {
                l.disassemble_chunk(vm, 0).unwrap();
                Ok(Value::Nil)
            }
            _ => Err(VMError::new_vm("DASM: Not a callable.")),
        },
        _ => Err(VMError::new_vm("DASM: Not a callable.")),
    }
}

const PROMPT_FN: &str = "prompt";
fn main() {
    let mut con = Context::new();

    con.history
        .set_file_name_and_load_history("history")
        .unwrap();
    let mut vm = Vm::new();
    vm.set_global("pr", Value::Builtin(CallFunc { func: pr }));
    vm.set_global("prn", Value::Builtin(CallFunc { func: prn }));
    vm.set_global("dasm", Value::Builtin(CallFunc { func: dasm }));
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
                let mut line = 1;
                for exp in exps {
                    if let Value::Reference(h) = exp {
                        if let Object::Pair(_, _, Some(meta)) = vm.get(h) {
                            line = meta.line as u32;
                        }
                    }
                    let mut state = CompileState::new_state(&mut vm, PROMPT_FN, line, None);
                    pass1(&mut vm, &mut state, exp).unwrap();
                    compile(&mut vm, &mut state, exp, 0, &mut line).unwrap();
                    state.chunk.encode0(RET, line).unwrap();
                    let chunk = Rc::new(state.chunk.clone());
                    if let Err(err) = vm.execute(chunk) {
                        println!("ERROR: {}", err);
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
                        println!("{}", vm.get_stack(0).display_value(&vm));
                    }
                }
            }
            Err(err) => println!("Reader error: {}", err),
        }
    }
}
