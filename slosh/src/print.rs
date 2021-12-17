use slvm::heap::*;
use slvm::value::*;
use slvm::vm::*;
use slvm::Interned;

fn is_sym(vm: &Vm, name: &str, intern: Interned) -> bool {
    if let Some(i) = vm.get_if_interned(name) {
        if intern == i {
            return true;
        }
    }
    false
}

fn quotey(vm: &Vm, car: Value, buf: &mut String) -> bool {
    if let Value::Symbol(i) = car {
        if is_sym(vm, "quote", i) {
            buf.push('\'');
            true
        } else if is_sym(vm, "back-quote", i) {
            buf.push('`');
            true
        } else if is_sym(vm, "unquote", i) {
            buf.push(',');
            true
        } else if is_sym(vm, "unquote-splice", i) {
            buf.push_str(",@");
            true
        } else if is_sym(vm, "unquote-splice!", i) {
            buf.push_str(",.");
            true
        } else {
            false
        }
    } else {
        false
    }
}

fn list_out_iter(vm: &Vm, res: &mut String, itr: &mut dyn Iterator<Item = Value>) {
    let mut first = true;
    for p in itr {
        if !first {
            res.push(' ');
        } else {
            first = false;
        }
        res.push_str(&display_value(vm, p));
    }
}

fn list_out(vm: &Vm, res: &mut String, lst: Value) {
    let mut first = true;
    let mut cdr = lst;
    loop {
        if let Value::Nil = cdr {
            break;
        }
        if !first {
            res.push(' ');
        } else {
            first = false;
        }
        match cdr {
            Value::Reference(h) => match vm.get(h) {
                Object::Pair(car, ncdr, _) => {
                    res.push_str(&car.display_value(vm));
                    cdr = *ncdr;
                }
                _ => {
                    res.push_str(". ");
                    res.push_str(&cdr.display_value(vm));
                    break;
                }
            },
            _ => {
                res.push_str(". ");
                res.push_str(&cdr.display_value(vm));
                break;
            }
        }
    }
}

pub fn display_value(vm: &Vm, val: Value) -> String {
    match &val {
        Value::True => "true".to_string(),
        Value::False => "false".to_string(),
        Value::Float(f) => format!("{}", f.0),
        Value::Int(i) => format!("{}", i),
        Value::UInt(i) => format!("{}", i),
        Value::Byte(b) => format!("{}", b),
        Value::Symbol(i) => vm.get_interned(*i).to_string(),
        Value::Keyword(i) => format!(":{}", vm.get_interned(*i).to_string()),
        Value::StringConst(i) => format!("\"{}\"", vm.get_interned(*i).to_string()),
        Value::CodePoint(ch) => format!("#\\{}", ch),
        Value::CharCluster(l, c) => {
            format!("#\\{}", String::from_utf8_lossy(&c[0..*l as usize]))
        }
        Value::CharClusterLong(_) => "Char".to_string(), // XXX TODO- move this to Object?
        Value::Builtin(_) => "#<Function>".to_string(),
        Value::Binding(_) => display_value(vm, val.unref(vm)),
        Value::Global(_) => display_value(vm, val.unref(vm)),
        Value::Nil => "nil".to_string(),
        Value::Undefined => "#<Undefined>".to_string(), //panic!("Tried to get type for undefined!"),
        Value::Reference(h) => match vm.get(*h) {
            Object::Lambda(_) => "#<Lambda>".to_string(),
            Object::Macro(_) => "#<Macro>".to_string(),
            Object::Closure(_, _) => "#<Lambda>".to_string(),
            Object::Vector(v) => {
                let mut res = String::new();
                res.push_str("#(");
                list_out_iter(vm, &mut res, &mut v.iter().copied());
                res.push(')');
                res
            }
            Object::Pair(car, cdr, _) => {
                let mut res = String::new();
                if quotey(vm, *car, &mut res) {
                    if let Some((cadr, Value::Nil)) = cdr.get_pair(vm) {
                        res.push_str(&display_value(vm, cadr));
                    } else {
                        res.push_str(&display_value(vm, *cdr));
                    }
                } else {
                    res.push('(');
                    list_out(vm, &mut res, val);
                    res.push(')');
                }
                res
            }
            Object::String(s) => format!("\"{}\"", s),
            Object::Bytes(_) => "Bytes".to_string(), // XXX TODO
        },
    }
}

pub fn pretty_value(vm: &Vm, val: Value) -> String {
    match &val {
        Value::StringConst(i) => vm.get_interned(*i).to_string(),
        Value::CodePoint(ch) => format!("{}", ch),
        Value::CharCluster(l, c) => {
            format!("{}", String::from_utf8_lossy(&c[0..*l as usize]))
        }
        Value::CharClusterLong(_) => "Char".to_string(),
        Value::Reference(h) => match vm.get(*h) {
            Object::String(s) => format!("{}", s),
            _ => display_value(vm, val),
        },
        _ => display_value(vm, val),
    }
}
