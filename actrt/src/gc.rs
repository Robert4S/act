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

    pub fn free_nonreachable(&mut self, reachable: Vec<Gc>) {
        let ptrs: BTreeSet<usize> = reachable.iter().map(|p| p.ptr).collect();
        let nonreachable = (0..(self.values.len())).filter(|v| !ptrs.contains(v));
        nonreachable.for_each(|ptr| self.free(ptr));
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

    #[inline(always)]
    fn free(&mut self, idx: usize) {
        self.values[idx] = None;
        self.free.insert(idx);
    }

    pub unsafe fn get(&self, idx: usize) -> &Value {
        // TODO: Change when debugging
        self.values.get_unchecked(idx).as_ref().unwrap_unchecked()
        //let reference = self
        //    .values
        //    .get(idx)
        //    .expect(&format!("Yeah {idx} is not in the backing array bucko"));
        //reference
        //    .as_ref()
        //    .expect(&format!("{idx} is not allocated"))
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Number(f64),
    String(String),
    Bool(bool),
    List(Vec<Gc>),
    Pid(Pid),
    Undefined(Undefined),
}

#[derive(Clone, Debug)]
pub enum Undefined {
    Creation,
    MakeUndefined,
}

impl Gc {
    pub fn mark(&self, runtime: &RT, marks: &mut Vec<Gc>) {
        if marks.contains(self) {
            return;
        }
        marks.push(self.clone());
        let value = runtime.deref_gc(self).clone();
        value.mark(runtime, marks);
    }
}

impl Value {
    pub fn to_string(&self, runtime: &RT) -> String {
        match self {
            Value::Number(n) => n.to_string(),
            Value::String(s) => s.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::List(vec) => format!(
                "{:?}",
                vec.iter()
                    .map(|g| runtime.deref_gc(g).to_string(runtime))
                    .collect::<Vec<_>>()
            ),
            Value::Pid(pid) => format!("PID({})", &pid.0),
            Value::Undefined(_) => "Undefined".to_string(),
        }
    }
    pub fn mark(&self, runtime: &RT, marks: &mut Vec<Gc>) {
        match self {
            Self::Number(_) => (),
            Self::String(_) => (),
            Self::Bool(_) => (),
            Self::List(v) => {
                for value in v {
                    value.mark(runtime, marks);
                }
            }
            Self::Pid(num) => runtime.find_reachable_vals(num, marks),
            Self::Undefined(_) => (),
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
    pub fn new(val: Value, runtime: &RT) -> Self {
        runtime.make_gc(val)
    }

    pub fn own_ptr(&self) -> usize {
        self.ptr
    }

    pub fn eval_ge(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 >= n2), runtime),
            _ => panic!("Mismatched types, expected numbers for ge, got {v1:?}, {v2:?}"),
        }
    }

    pub fn eval_greater(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 > n2), runtime),
            _ => panic!("Mismatched types, expected numbers for greater"),
        }
    }

    pub fn eval_le(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 <= n2), runtime),
            _ => panic!("Mismatched types, expected numbers for le, got {v1:?}, {v2:?}"),
        }
    }

    pub fn eval_lesser(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Bool(n1 < n2), runtime),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_and(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Bool(b1), Value::Bool(b2)) => Gc::new(Value::Bool(*b1 && *b2), runtime),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_or(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Bool(b1), Value::Bool(b2)) => Gc::new(Value::Bool(*b1 || *b2), runtime),
            _ => panic!("Mismatched types, expected numbers for lesser"),
        }
    }

    pub fn eval_eq(&self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(self);
        let v2: &Value = runtime.deref_gc(&rhs);

        Gc::new(Value::Bool(v1.equals(v2, runtime)), runtime)
    }

    pub fn eval_add(self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 + n2), runtime),
            _ => panic!("Mismatched types, expected numbers for add"),
        }
    }

    pub fn eval_sub(self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 - n2), runtime),
            _ => panic!("Mismatched types, expected numbers for minus, got {v1:?}, {v2:?}"),
        }
    }

    pub fn eval_mul(self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 * n2), runtime),
            _ => panic!("Mismatched types, expected numbers for mul"),
        }
    }

    pub fn eval_div(self, rhs: Self, runtime: &RT) -> Gc {
        let v1: &Value = runtime.deref_gc(&self);
        let v2: &Value = runtime.deref_gc(&rhs);

        match (v1, v2) {
            (Value::Number(n1), Value::Number(n2)) => Gc::new(Value::Number(n1 / n2), runtime),
            _ => panic!("Mismatched types, expected numbers for div"),
        }
    }
}
