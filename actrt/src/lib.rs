use std::{ffi::CStr, mem, process::exit};

use gc::{Gc, Value};
use runtime::{Pid, RUNTIME};

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

mod gc;
mod runtime;

#[no_mangle]
pub unsafe extern "C" fn make_actor(init: *const u8, update: *const u8) -> Pid {
    let init = mem::transmute::<*const u8, extern "C" fn() -> Gc>(init);
    let update = mem::transmute::<*const u8, extern "C" fn(Gc, Gc) -> Gc>(update);
    RUNTIME.make_actor(init, update)
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_number(number: f32) -> Gc {
    Gc::new(Value::Number(number))
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_bool(bool: usize) -> Gc {
    let b = if bool == 0 { false } else { true };
    Gc::new(Value::Bool(b))
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_string(string: *const i8) -> Gc {
    let s = CStr::from_ptr(string);
    Gc::new(Value::String(s.to_str().unwrap().to_owned()))
}

#[no_mangle]
pub unsafe extern "C" fn make_undefined() -> Gc {
    Gc::new(Value::Undefined)
}

#[no_mangle]
pub unsafe extern "C" fn eval_conditional(cond: Gc) -> usize {
    let cond: &Value = &cond;
    match cond {
        Value::Bool(b) => {
            if *b {
                1
            } else {
                0
            }
        }
        _ => panic!("Conditional is not a boolean"),
    }
}

#[no_mangle]
pub unsafe extern "C" fn send_actor(actor: Gc, value: Gc) {
    let actor: &Value = &actor;
    match actor {
        Value::Pid(p) => RUNTIME.send_actor(p.clone(), value),
        _ => panic!("Actor pid is not a pid"),
    }
}

#[no_mangle]
pub unsafe extern "C" fn start_runtime() {
    println!("{:?}", RUNTIME);
    exit(0);
}

#[cfg(test)]
mod tests {
    use super::*;
}
