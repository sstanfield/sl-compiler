use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use slvm::chunk::*;
use slvm::interner::*;
use slvm::value::*;
use slvm::vm::*;

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
    pub captures: Captures,
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
        let data_d = self.data.borrow();
        if let Some(idx) = data_d.syms.get(&key) {
            Some(*idx)
        } else {
            if let Some(outer) = &self.outer {
                drop(data_d);
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

pub struct CompileState {
    pub symbols: Rc<RefCell<Symbols>>,
    pub constants: HashMap<Value, usize>,
    pub chunk: Chunk,
}

impl CompileState {
    pub fn new() -> Self {
        CompileState {
            symbols: Rc::new(RefCell::new(Symbols::with_outer(None))),
            constants: HashMap::new(),
            chunk: Chunk::new("no_file", 1),
        }
    }

    pub fn new_state(
        file_name: &'static str,
        first_line: u32,
        outer: Rc<RefCell<Symbols>>,
    ) -> Self {
        let symbols = Rc::new(RefCell::new(Symbols::with_outer(Some(outer))));
        CompileState {
            symbols,
            constants: HashMap::new(),
            chunk: Chunk::new(file_name, first_line),
        }
    }

    pub fn new_temp(state: &CompileState, line: u32) -> Self {
        CompileState {
            symbols: state.symbols.clone(),
            constants: HashMap::new(),
            chunk: Chunk::new(state.chunk.file_name, line),
        }
    }

    pub fn reserved_regs(&self) -> usize {
        self.symbols.borrow().len() + 1
    }

    pub fn get_symbol(&self, sym: Interned) -> Option<usize> {
        self.symbols.borrow().data.borrow().syms.get(&sym).copied()
    }

    pub fn add_constant(&mut self, exp: Value) -> usize {
        if let Some(i) = self.constants.get(&exp) {
            *i
        } else {
            let const_i = self.chunk.add_constant(exp);
            self.constants.insert(exp, const_i);
            const_i
        }
    }
}

impl Default for CompileState {
    fn default() -> Self {
        Self::new()
    }
}
