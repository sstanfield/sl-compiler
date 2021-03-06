use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use slvm::chunk::*;
use slvm::interner::*;
use slvm::value::*;
use slvm::vm::*;

#[derive(Clone, Debug)]
pub struct SymbolsInt {
    pub syms: HashMap<Interned, usize>,
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
    pub captures: Captures,
}

impl Symbols {
    pub fn with_outer(outer: Option<Rc<RefCell<Symbols>>>) -> Symbols {
        let data = Rc::new(RefCell::new(SymbolsInt {
            syms: HashMap::new(),
            count: 0,
        }));
        Symbols {
            data,
            outer,
            //namespace,
            captures: Rc::new(RefCell::new(Vec::new())),
        }
    }

    pub fn with_let(source: Rc<RefCell<Symbols>>, result: usize) -> Symbols {
        let data = Rc::new(RefCell::new(SymbolsInt {
            syms: HashMap::new(),
            count: 0,
        }));
        {
            let mut datad = data.borrow_mut();
            for (key, val) in source.borrow().data.borrow().syms.iter() {
                datad.syms.insert(*key, *val);
            }
            if result > 0 {
                datad.count = result - 1;
            }
        }
        Symbols {
            data,
            outer: source.borrow().outer.clone(),
            //namespace,
            captures: source.borrow().captures.clone(),
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

pub struct Specials {
    pub def: Interned,
    pub set: Interned,
    pub do_: Interned,
    pub fn_: Interned,
    pub mac_: Interned,
    pub if_: Interned,
    pub add: Interned,
    pub sub: Interned,
    pub mul: Interned,
    pub div: Interned,
    pub inc: Interned,
    pub dec: Interned,
    pub list: Interned,
    pub list_append: Interned,
    pub cons: Interned,
    pub car: Interned,
    pub cdr: Interned,
    pub xar: Interned,
    pub xdr: Interned,
    pub vec: Interned,
    pub make_vec: Interned,
    pub vec_pop: Interned,
    pub vec_push: Interned,
    pub vec_nth: Interned,
    pub vec_set: Interned,
    pub quote: Interned,
    pub backquote: Interned,
    pub recur: Interned,
    pub this_fn: Interned,
    pub numeq: Interned,
    pub numneq: Interned,
    pub numlt: Interned,
    pub numlte: Interned,
    pub numgt: Interned,
    pub numgte: Interned,
    pub eq: Interned,
    pub equal: Interned,
    pub type_: Interned,
    pub not: Interned,
    pub and: Interned,
    pub or: Interned,
    pub err: Interned,
    pub vec_len: Interned,
    pub vec_clr: Interned,
    pub str_: Interned,
    pub let_: Interned,
    pub letstar: Interned,
    pub call_cc: Interned,
    pub defer: Interned,
    pub on_error: Interned,

    pub rest: Interned,
}

impl Specials {
    pub fn new(vm: &mut Vm) -> Self {
        Self {
            def: vm.intern_static("def"),
            set: vm.intern_static("set!"),
            do_: vm.intern_static("do"),
            fn_: vm.intern_static("fn"),
            mac_: vm.intern_static("macro"),
            if_: vm.intern_static("if"),
            add: vm.intern_static("+"),
            sub: vm.intern_static("-"),
            mul: vm.intern_static("*"),
            div: vm.intern_static("/"),
            inc: vm.intern_static("inc!"),
            dec: vm.intern_static("dec!"),
            list: vm.intern_static("list"),
            list_append: vm.intern_static("list-append"),
            cons: vm.intern_static("cons"),
            car: vm.intern_static("car"),
            cdr: vm.intern_static("cdr"),
            xar: vm.intern_static("xar!"),
            xdr: vm.intern_static("xdr!"),
            vec: vm.intern_static("vec"),
            make_vec: vm.intern_static("make-vec"),
            vec_push: vm.intern_static("vec-push!"),
            vec_pop: vm.intern_static("vec-pop!"),
            vec_nth: vm.intern_static("vec-nth"),
            vec_set: vm.intern_static("vec-set!"),
            quote: vm.intern_static("quote"),
            backquote: vm.intern_static("back-quote"),
            recur: vm.intern_static("recur"),
            this_fn: vm.intern_static("this-fn"),
            numeq: vm.intern_static("="),
            numneq: vm.intern_static("/="),
            numlt: vm.intern_static("<"),
            numlte: vm.intern_static("<="),
            numgt: vm.intern_static(">"),
            numgte: vm.intern_static(">="),
            eq: vm.intern_static("eq?"),
            equal: vm.intern_static("equal?"),
            type_: vm.intern_static("type"),
            not: vm.intern_static("not"),
            and: vm.intern_static("and"),
            or: vm.intern_static("or"),
            err: vm.intern_static("err"),
            vec_len: vm.intern_static("vec-len"),
            vec_clr: vm.intern_static("vec-clear!"),
            str_: vm.intern_static("str"),
            let_: vm.intern_static("let"),
            letstar: vm.intern_static("let*"),
            call_cc: vm.intern_static("call/cc"),
            defer: vm.intern_static("defer"),
            on_error: vm.intern_static("on-error"),

            rest: vm.intern_static("&rest"),
        }
    }
}

pub struct CompileState {
    pub symbols: Rc<RefCell<Symbols>>,
    pub constants: HashMap<Value, usize>,
    pub chunk: Chunk,
    pub specials: Specials,
    pub max_regs: usize,
    pub tail: bool,
    pub defers: usize,
}

impl CompileState {
    pub fn new(vm: &mut Vm) -> Self {
        CompileState {
            symbols: Rc::new(RefCell::new(Symbols::with_outer(None))),
            constants: HashMap::new(),
            chunk: Chunk::new("no_file", 1),
            specials: Specials::new(vm),
            max_regs: 0,
            tail: false,
            defers: 0,
        }
    }

    pub fn new_state(
        vm: &mut Vm,
        file_name: &'static str,
        first_line: u32,
        outer: Option<Rc<RefCell<Symbols>>>,
    ) -> Self {
        let symbols = Rc::new(RefCell::new(Symbols::with_outer(outer)));
        CompileState {
            symbols,
            constants: HashMap::new(),
            chunk: Chunk::new(file_name, first_line),
            specials: Specials::new(vm),
            max_regs: 0,
            tail: false,
            defers: 0,
        }
    }

    pub fn new_temp(vm: &mut Vm, state: &CompileState, line: u32) -> Self {
        CompileState {
            symbols: state.symbols.clone(),
            constants: HashMap::new(),
            chunk: Chunk::new(state.chunk.file_name, line),
            specials: Specials::new(vm),
            max_regs: state.max_regs,
            tail: state.tail,
            defers: state.defers,
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
