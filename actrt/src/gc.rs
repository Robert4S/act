use std::{ops::Deref, sync::Mutex};

use crate::runtime::{Pid, RUNTIME};

#[derive(Debug)]
pub struct Allocator {
    values: Mutex<Vec<Option<Value>>>,
    free: Mutex<Vec<usize>>,
}

impl Allocator {
    pub fn new() -> Self {
        Self {
            values: Mutex::new(Vec::new()),
            free: Mutex::new(Vec::new()),
        }
    }

    pub fn alloc(&self, value: Value) -> usize {
        if let Some(idx) = self.free.lock().unwrap().pop() {
            self.values.lock().unwrap()[idx] = Some(value);
            idx
        } else {
            let mut values = self.values.lock().unwrap();
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
        let mut values = self.values.lock().unwrap();

        let not_marked = (0..(values.len() - 1))
            .filter(|key| !marks.contains(key))
            .collect::<Vec<usize>>();

        let mut free = self.free.lock().unwrap();
        not_marked.into_iter().for_each(|key| {
            values[key] = None;
            free.push(key);
        });
    }

    pub unsafe fn get(&self, idx: usize) -> &Value {
        let b = self.values.lock().unwrap();
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
    Undefined,
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
            Self::Undefined => panic!("Value is not defined"),
        }
    }
}

#[repr(C)]
#[derive(Clone, Debug)]
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
        let ptr = RUNTIME.allocator.alloc(val);
        Self { ptr }
    }

    pub fn own_ptr(&self) -> usize {
        self.ptr
    }
}

impl Deref for Gc {
    type Target = Value;
    fn deref(&self) -> &Self::Target {
        unsafe {
            let val = RUNTIME.allocator.get(self.ptr) as *const Value;
            &*val
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

    RUNTIME.allocator.mark_and_sweep(vec![values.clone()]);
    assert_exists!(values);

    let values: &Value = &values;
    match values {
        Value::List(vs) => vs.iter().for_each(|v| assert_exists!(v)),
        _ => panic!("what the fuck buddy"),
    }

    assert_not_exists!(bool_value);
    assert_not_exists!(number_value);
}
