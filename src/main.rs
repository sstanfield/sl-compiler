use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use slvm::vm::*;

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
        let outer = syms.as_ref().map(|lex_syms| Rc::new(RefCell::new(lex_syms.clone())));
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

fn main() {
    println!("Hello, world!");
}
