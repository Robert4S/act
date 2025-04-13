use core::panic;
use std::collections::BTreeSet;

use super::runtime::{Pid, RT};

#[derive(Debug)]
pub struct Allocator {
    pub values: Vec<Option<Value>>,
    pub free: BTreeSet<usize>,
}

impl Allocator {
    pub fn new() -> Self {
        Self {
            values: Vec::new(),
            free: BTreeSet::new(),
        }
    }

    pub fn alloc(&mut self, value: Value) -> usize {
        if let Some(idx) = self.free.pop_first() {
            self.values[idx] = Some(value);
            idx
        } else {
            self.values.push(Some(value));
            self.values.len() - 1
        }
    }

    pub unsafe fn sweep(&mut self, not_marked: Vec<usize>) -> () {
        not_marked.into_iter().for_each(|key| {
            self.free(key);
        });
    }

    #[inline(always)]
    fn free(&mut self, idx: usize) {
        self.values[idx] = None;
        self.free.insert(idx);
    }

    pub unsafe fn get(&self, idx: usize) -> &Value {
        let reference = self
            .values
            .get(idx)
            .expect(&format!("Yeah {idx} is not in the backing array bucko"));
        match reference {
            Some(v) => unsafe { &*(v as *const Value) },
            None => panic!("Invalid dereference {idx}"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Number(f32),
    String(String),
    Bool(bool),
    List(Vec<Gc>),
    Pid(Pid),
    Undefined(String),
}

impl Gc {
    pub fn mark(&self, runtime: &RT) -> Vec<Gc> {
        let value = runtime.deref_gc(self).clone();
        let mut value_marked = value.mark(runtime);
        value_marked.push(self.clone());
        value_marked
    }
}

impl Value {
    pub fn mark(&self, runtime: &RT) -> Vec<Gc> {
        match self {
            Self::Number(_) => vec![],
            Self::String(_) => vec![],
            Self::Bool(_) => vec![],
            Self::List(v) => v
                .iter()
                .map(|v| {
                    let mut marks = v.mark(runtime);
                    marks.push(v.clone());
                    marks
                })
                .flatten()
                .collect(),
            Self::Pid(num) => runtime.mark_actor(num),
            Self::Undefined(_) => vec![],
        }
    }

    pub fn equals(&self, other: &Self, runtime: &RT) -> bool {
        match (self, other) {
            (Self::Number(n1), Self::Number(n2)) => n1 == n2,
            (Self::Bool(b1), Self::Bool(b2)) => b1 == b2,
            (Self::String(s1), Self::String(s2)) => s1 == s2,
            (Self::Pid(p1), Self::Pid(p2)) => p1 == p2,
            (Self::List(l1), Self::List(l2)) => l1
                .iter()
                .zip(l2.iter())
                .all(|(v1, v2)| runtime.deref_gc(v1).equals(runtime.deref_gc(v2), runtime)),
            _ => false,
        }
    }
}

#[repr(C)]
#[derive(Clone, Debug, Copy, PartialEq, Eq)]
pub struct Gc {
    pub ptr: usize,
}

impl Gc {
    pub fn new(val: Value, runtime: &mut RT) -> Self {
        runtime.make_gc(val)
    }

    pub fn own_ptr(&self) -> usize {
        self.ptr
    }

    pub fn eval_ge(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 >= n2), runtime),
            _ => panic!("Mismatched types, expected numbers for ge, got {v1:?}, {v2:?}"),
        }
    }

    pub fn eval_greater(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 > n2), runtime),
            _ => panic!("Mismatched types, expected numbers for greater"),
        }
    }

    pub fn eval_le(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 <= n2), runtime),
            _ => panic!("Mismatched types, expected numbers for le, got {v1:?}, {v2:?}"),
        }
    }

    pub fn eval_lesser(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 < n2), runtime),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_and(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Bool(b1), Value::Bool(b2)) => Gc::new(Value::Bool(*b1 && *b2), runtime),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_or(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Bool(b1), Value::Bool(b2)) => Gc::new(Value::Bool(*b1 || *b2), runtime),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_eq(&self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        Gc::new(Value::Bool(v1.equals(v2, runtime)), runtime)
    }

    pub fn eval_add(self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 + n2), runtime),
            _ => panic!("Mismatched types, expected numbers for add"),
        }
    }

    pub fn eval_sub(self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 - n2), runtime),
            _ => panic!("Mismatched types, expected numbers for minus, got {v1:?}, {v2:?}"),
        }
    }

    pub fn eval_mul(self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 * n2), runtime),
            _ => panic!("Mismatched types, expected numbers for mul"),
        }
    }

    pub fn eval_div(self, rhs: Self, runtime: &mut RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 / n2), runtime),
            _ => panic!("Mismatched types, expected numbers for div"),
        }
    }
}
