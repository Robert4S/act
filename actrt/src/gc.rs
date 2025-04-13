use std::{
    ops::{self, Deref},
    panic,
    sync::{LazyLock, Mutex, MutexGuard},
};

use crate::runtime::{get_runtime, Pid, Runtime};

#[derive(Debug)]
pub struct Allocator {
    pub values: Mutex<Vec<Option<Value>>>,
    free: Mutex<Vec<usize>>,
}

impl Allocator {
    #[track_caller]
    fn lock_value(&self) -> MutexGuard<Vec<Option<Value>>> {
        let caller = panic::Location::caller();
        println!("called from {}", caller);
        self.values.lock().unwrap()
    }

    pub fn new() -> Self {
        Self {
            values: Mutex::new(Vec::new()),
            free: Mutex::new(Vec::new()),
        }
    }

    pub fn alloc(&self, value: Value) -> usize {
        if let Some(idx) = self.free.lock().unwrap().pop() {
            self.lock_value()[idx] = Some(value);
            idx
        } else {
            let mut values = self.lock_value();
            values.push(Some(value));
            values.len() - 1
        }
    }

    pub fn mark_and_sweep(&self, roots: Vec<Gc>) {
        let t = roots.clone();
        let root_values = t.iter().map(|ptr| {
            let x: &Value = ptr;
            x
        });

        let mut marks = root_values
            .map(Value::mark)
            .flatten()
            .map(|p| p.own_ptr())
            .chain(roots.iter().map(|p| p.own_ptr()))
            .collect::<Vec<usize>>();

        marks.dedup();
        let not_marked = {
            let values = self.lock_value();

            (0..(values.len() - 1))
                .filter(|key| !marks.contains(key))
                .collect::<Vec<usize>>()
        };

        unsafe { self.sweep(not_marked) }
    }

    pub unsafe fn sweep(&self, not_marked: Vec<usize>) -> () {
        let mut values = self.lock_value();
        let mut free = self.free.lock().unwrap();
        not_marked.into_iter().for_each(|key| {
            values[key] = None;
            free.push(key);
        });
    }

    pub unsafe fn get(&self, idx: usize) -> &Value {
        let b = self.lock_value();
        let reference = b.get(idx).unwrap();
        match reference {
            Some(v) => unsafe { &*(v as *const Value) },
            None => panic!("Invalid dereference {idx}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Number(f32),
    String(String),
    Bool(bool),
    List(Vec<Gc>),
    Pid(Pid),
    Undefined(String),
}

impl Gc {
    pub fn mark(&self) -> Vec<Gc> {
        let mut value_marked = Value::mark(self);
        value_marked.push(self.clone());
        value_marked
    }
}

impl Value {
    pub fn mark(&self) -> Vec<Gc> {
        match self {
            Self::Number(_) => vec![],
            Self::String(_) => vec![],
            Self::Bool(_) => vec![],
            Self::List(v) => v
                .iter()
                .map(|v| {
                    let mut marks = v.mark();
                    marks.push(v.clone());
                    marks
                })
                .flatten()
                .collect(),
            Self::Pid(num) => num.mark(),
            Self::Undefined(_) => vec![],
        }
    }
}

#[repr(C)]
#[derive(Clone, Debug, Copy)]
pub struct Gc {
    ptr: usize,
}

impl PartialEq for Gc {
    fn eq(&self, other: &Self) -> bool {
        let own_inner: &Value = self;
        let other_inner: &Value = other;
        Value::eq(own_inner, other_inner)
    }
}

impl Eq for Gc {
    fn assert_receiver_is_total_eq(&self) {
        ()
    }
}

impl Gc {
    pub fn new(val: Value) -> Self {
        let ptr = get_runtime().allocator.alloc(val);
        Self { ptr }
    }

    pub fn own_ptr(&self) -> usize {
        self.ptr
    }

    pub fn eval_ge(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 >= n2)),
            _ => panic!("Mismatched types, expected numbers for ge"),
        }
    }

    pub fn eval_greater(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 > n2)),
            _ => panic!("Mismatched types, expected numbers for greater"),
        }
    }

    pub fn eval_le(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 <= n2)),
            _ => panic!("Mismatched types, expected numbers for le"),
        }
    }

    pub fn eval_lesser(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 < n2)),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_and(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Bool(b1), Value::Bool(b2)) => Gc::new(Value::Bool(*b1 && *b2)),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_or(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Bool(b1), Value::Bool(b2)) => Gc::new(Value::Bool(*b1 || *b2)),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_eq(&self, rhs: Self) -> Gc {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        Gc::new(Value::Bool(Value::eq(v1, v2)))
    }
}

impl Deref for Gc {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        unsafe {
            let val = get_runtime().allocator.get(self.ptr) as *const Value;
            &*val
        }
    }
}

impl ops::Add for Gc {
    type Output = Gc;
    fn add(self, rhs: Self) -> Self::Output {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 + n2)),
            _ => panic!("Mismatched types, expected numbers for add"),
        }
    }
}

impl ops::Sub for Gc {
    type Output = Gc;
    fn sub(self, rhs: Self) -> Self::Output {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 - n2)),
            _ => panic!("Mismatched types, expected numbers for minus"),
        }
    }
}

impl ops::Mul for Gc {
    type Output = Gc;
    fn mul(self, rhs: Self) -> Self::Output {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 * n2)),
            _ => panic!("Mismatched types, expected numbers for mul"),
        }
    }
}

impl ops::Div for Gc {
    type Output = Gc;
    fn div(self, rhs: Self) -> Self::Output {
        let v1: &Value = &self;
        let v2: &Value = &rhs;

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 / n2)),
            _ => panic!("Mismatched types, expected numbers for div"),
        }
    }
}

macro_rules! assert_exists {
    ($val:expr) => {{
        let is_ok = std::panic::catch_unwind(|| {
            let _: &Value = &$val;
        })
        .is_ok();
        assert!(
            is_ok,
            "Allocation {:?} does not exist or has been free'd",
            $val
        );
    }};
}

macro_rules! assert_not_exists {
    ($val:expr) => {{
        std::panic::set_hook(Box::new(|_| {}));
        let is_ok = std::panic::catch_unwind(|| {
            let _: &Value = &$val;
        })
        .is_ok();
        assert!(!is_ok, "Allocation {:?} has not been free'd", $val);
    }};
}

pub fn test() {
    let bool_value = Gc::new(Value::Bool(true));
    let number_value = Gc::new(Value::Number(13.6));
    let values = Gc::new(Value::List(
        (0..10000)
            .map(|n| Gc::new(Value::Number(n as f32)))
            .collect(),
    ));

    get_runtime().allocator.mark_and_sweep(vec![values.clone()]);
    assert_exists!(values);

    let values: &Value = &values;
    match values {
        Value::List(vs) => vs.iter().for_each(|v| assert_exists!(v)),
        _ => panic!("what the fuck buddy"),
    }

    assert_not_exists!(bool_value);
    assert_not_exists!(number_value);
}
