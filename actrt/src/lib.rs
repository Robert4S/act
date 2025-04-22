use std::{
    ffi::CStr,
    sync::{Arc, LazyLock},
};

use gc::{Gc, Undefined, Value};
use runtime::RT;

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

//mod gc;
mod gc;
//mod runtime;
mod runtime;

static RT: LazyLock<Arc<RT>> = LazyLock::new(|| Arc::new(RT::new()));

#[no_mangle]
pub extern "C" fn make_actor(
    rt: &RT,
    init: extern "C" fn(&RT) -> Gc,
    update: extern "C" fn(&RT, Gc, Gc) -> Gc,
) -> Gc {
    rt.make_gc(Value::Pid(rt.make_actor(init, update)))
}

#[no_mangle]
pub extern "C" fn make_gc_unit(rt: &RT) -> Gc {
    rt.make_gc(Value::Unit)
}

#[no_mangle]
pub extern "C" fn make_actor_global(
    init: extern "C" fn(&RT) -> Gc,
    update: extern "C" fn(&RT, Gc, Gc) -> Gc,
    slot: *mut Gc,
) {
    unsafe {
        let val = RT.make_gc(Value::Pid(RT.make_actor(init, update)));
        *slot = val;
        RT.make_static(val);
    }
}

#[no_mangle]
pub extern "C" fn make_gc_number(rt: &RT, number: f64) -> Gc {
    let res = rt.make_gc(Value::Number(number));
    res
}

#[no_mangle]
pub extern "C" fn make_gc_bool(rt: &RT, bool: usize) -> Gc {
    let b = if bool == 0 { false } else { true };
    rt.make_gc(Value::Bool(b))
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_string(rt: &RT, string: *const i8) -> Gc {
    let s = CStr::from_ptr(string);
    rt.make_gc(Value::String(s.to_str().unwrap().to_owned()))
}

#[no_mangle]
pub extern "C" fn make_undefined(rt: &RT) -> Gc {
    rt.make_gc(Value::Undefined(Undefined::MakeUndefined))
}

#[no_mangle]
pub extern "C" fn eval_conditional(rt: &RT, cond: Gc) -> usize {
    let cond: Value = rt.deref_gc(&cond).clone();
    match cond {
        Value::Bool(b) => {
            if b {
                1
            } else {
                0
            }
        }
        _ => panic!("Conditional is not a boolean"),
    }
}

#[no_mangle]
pub extern "C" fn eval_plus(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_add(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_minus(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_sub(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_div(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_div(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_mul(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_mul(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_ge(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_ge(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_greater(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_greater(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_le(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_le(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_lesser(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_lesser(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_and(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_and(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_or(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_or(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn eval_eq(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_eq(rhs, runtime)
}

#[no_mangle]
pub extern "C" fn send_actor(runtime: &RT, actor: Gc, value: Gc) {
    runtime.send_actor(actor, value);
}

#[no_mangle]
pub extern "C" fn start_runtime() {
    RT.init_actors();
    RT::supervise(RT.clone());
}

#[no_mangle]
pub unsafe extern "C" fn make_static(value: Gc) -> () {
    RT.make_static(value);
}

#[no_mangle]
pub unsafe extern "C" fn print_value(rt: &RT, val: Gc) {
    let val = rt.deref_gc(&val).to_string(rt);
    print!("{val}");
}

//use gc::{Gc, Undefined, Value};
//use runtime::{Init, Update, RT};

//static RT: LazyLock<Arc<Mutex<RT>>> = LazyLock::new(|| Arc::new(Mutex::new(RT::new())));

//#[track_caller]
//pub fn get_rt() -> &'static Arc<Mutex<RT>> {
//    &RT
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_actor(rt: &mut RT, init: *const u8, update: *const u8) -> Gc {
//    let init = mem::transmute::<*const u8, Init>(init);
//    let update = mem::transmute::<*const u8, Update>(update);
//    let pid = rt.make_actor(get_rt(), init, update);
//    rt.make_gc(Value::Pid(pid))
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_actor_global(
//    init: *const u8,
//    update: *const u8,
//    slot: *mut Gc,
//) -> Gc {
//    let mut rt = get_rt().lock().unwrap();
//    let init = mem::transmute::<*const u8, Init>(init);
//    let update = mem::transmute::<*const u8, Update>(update);
//    let pid = rt.make_actor(get_rt(), init, update);
//    let v = rt.make_gc(Value::Pid(pid));
//    *slot = v;
//    rt.make_static(v);
//    v
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_daemon(init: *const u8, update: *const u8, slot: *mut Gc) -> Gc {
//    let mut rt = get_rt().lock().unwrap();
//    let init = mem::transmute::<*const u8, Init>(init);
//    let update = mem::transmute::<*const u8, Update>(update);
//    let pid = rt.make_daemon(get_rt(), init, update);
//    let ptr = rt.make_gc(Value::Pid(pid));
//    *slot = ptr;
//    rt.make_static(ptr);
//    ptr
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_gc_number(rt: &mut RT, number: f32) -> Gc {
//    let res = rt.make_gc(Value::Number(number));
//    res
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_gc_bool(rt: &mut RT, bool: usize) -> Gc {
//    let b = if bool == 0 { false } else { true };
//    rt.make_gc(Value::Bool(b))
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_gc_string(rt: &mut RT, string: *const i8) -> Gc {
//    let s = CStr::from_ptr(string);
//    rt.make_gc(Value::String(s.to_str().unwrap().to_owned()))
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_undefined(rt: &mut RT) -> Gc {
//    rt.make_gc(Value::Undefined(Undefined::MakeUndefined))
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_conditional(rt: &mut RT, cond: Gc) -> usize {
//    let cond: Value = rt.deref_gc(&cond).clone();
//    match cond {
//        Value::Bool(b) => {
//            if b {
//                1
//            } else {
//                0
//            }
//        }
//        _ => panic!("Conditional is not a boolean"),
//    }
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_plus(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_add(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_minus(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_sub(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_div(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_div(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_mul(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_mul(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_ge(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_ge(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_greater(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_greater(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_le(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_le(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_lesser(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_lesser(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_and(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_and(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_or(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_or(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn eval_eq(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
//    lhs.eval_eq(rhs, runtime)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn send_actor(runtime: &mut RT, actor: Gc, value: Gc) {
//    runtime.send_actor(actor, value);
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn start_runtime() {
//    let with_gc: bool = env::var("ACT_ENABLE_GC")
//        .unwrap_or(String::from("true"))
//        .parse()
//        .unwrap();
//    RT::start_runtime(get_rt());
//    RT::supervise(with_gc);
//    exit(0)
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn make_static(value: Gc) -> () {
//    get_rt().lock().unwrap().make_static(value);
//}
//
//#[no_mangle]
//pub unsafe extern "C" fn print_value(rt: &mut RT, val: Gc) {
//    let val = rt.deref_gc(&val).to_string(rt);
//    print!("{val}");
//}

#[cfg(test)]
mod tests {

    use super::*;
    static mut FACT: Gc = Gc { ptr: 0 };
    extern "C" fn init(rt: &RT) -> Gc {
        let num = make_gc_number(rt, 5.);
        unsafe {
            send_actor(rt, FACT, num);
        }
        let state = make_gc_number(rt, 1.);
        return state;
    }

    extern "C" fn update(rt: &RT, arg: Gc, state: Gc) -> Gc {
        let stop_value = unsafe {
            make_gc_string(
                rt,
                b"I am done with my work here\0" as *const [u8; 28] as *const i8,
            )
        };

        let one_for_cmp = make_gc_number(rt, 1.);
        let one_for_minus = make_gc_number(rt, 1.);

        let le_res = eval_le(rt, arg, one_for_cmp);
        let cond_res = eval_conditional(rt, le_res);

        if cond_res == 1 {
            return stop_value;
        } else {
            let minused = eval_minus(rt, arg, one_for_minus);
            unsafe {
                send_actor(rt, FACT, minused);
            }
            let timesd = eval_mul(rt, arg, state);
            unsafe {
                send_actor(rt, PRINTER, timesd);
            }
            return timesd;
        }
    }

    #[test]
    fn test_factorial() {
        make_actor_global(init, update, &raw mut FACT);

        make_actor_global(init, update, &raw mut PRINTER);

        start_runtime();
    }

    static mut PRINTER: Gc = Gc { ptr: 0 };

    extern "C" fn init_printer(rt: &RT) -> Gc {
        make_gc_number(rt, -1.)
    }

    extern "C" fn update_printer(rt: &RT, state: Gc, arg: Gc) -> Gc {
        let arg_val = rt.deref_gc(&arg);
        println!("{:?}", arg_val);
        state
    }
}
