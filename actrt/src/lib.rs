use std::{
    env,
    ffi::CStr,
    mem,
    process::exit,
    sync::{Arc, LazyLock, Mutex},
};

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

mod gc;
mod runtime;

use gc::{Gc, Undefined, Value};
use runtime::{Init, Update, RT};

static RT: LazyLock<Arc<Mutex<RT>>> = LazyLock::new(|| Arc::new(Mutex::new(RT::new())));

#[track_caller]
pub fn get_rt() -> &'static Arc<Mutex<RT>> {
    &RT
}

#[no_mangle]
pub unsafe extern "C" fn make_actor(rt: &mut RT, init: *const u8, update: *const u8) -> Gc {
    let init = mem::transmute::<*const u8, Init>(init);
    let update = mem::transmute::<*const u8, Update>(update);
    let pid = rt.make_actor(get_rt(), init, update);
    rt.make_gc(Value::Pid(pid))
}

#[no_mangle]
pub unsafe extern "C" fn make_actor_global(init: *const u8, update: *const u8) -> Gc {
    let mut rt = get_rt().lock().unwrap();
    let init = mem::transmute::<*const u8, Init>(init);
    let update = mem::transmute::<*const u8, Update>(update);
    let pid = rt.make_actor(get_rt(), init, update);
    rt.make_gc(Value::Pid(pid))
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_number(rt: &mut RT, number: f32) -> Gc {
    let res = rt.make_gc(Value::Number(number));
    res
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_bool(rt: &mut RT, bool: usize) -> Gc {
    let b = if bool == 0 { false } else { true };
    rt.make_gc(Value::Bool(b))
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_string(rt: &mut RT, string: *const i8) -> Gc {
    let s = CStr::from_ptr(string);
    rt.make_gc(Value::String(s.to_str().unwrap().to_owned()))
}

#[no_mangle]
pub unsafe extern "C" fn make_undefined(rt: &mut RT) -> Gc {
    rt.make_gc(Value::Undefined(Undefined::MakeUndefined))
}

#[no_mangle]
pub unsafe extern "C" fn eval_conditional(rt: &mut RT, cond: Gc) -> usize {
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
pub unsafe extern "C" fn eval_plus(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_add(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_minus(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_sub(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_div(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_div(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_mul(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_mul(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_ge(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_ge(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_greater(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_greater(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_le(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_le(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_lesser(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_lesser(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_and(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_and(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_or(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_or(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn eval_eq(runtime: &mut RT, lhs: Gc, rhs: Gc) -> Gc {
    lhs.eval_eq(rhs, runtime)
}

#[no_mangle]
pub unsafe extern "C" fn send_actor(runtime: &mut RT, actor: Gc, value: Gc) {
    runtime.send_actor(actor, value);
}

#[no_mangle]
pub unsafe extern "C" fn start_runtime() {
    let with_gc: bool = env::var("ACT_ENABLE_GC")
        .unwrap_or(String::from("true"))
        .parse()
        .unwrap();
    RT::start_runtime(get_rt());
    RT::supervise(with_gc);
    exit(0)
}

#[no_mangle]
pub unsafe extern "C" fn make_static(value: Gc) -> () {
    get_rt().lock().unwrap().make_static(value);
}

#[cfg(test)]
mod tests {

    use super::*;
    static mut FACT: Gc = Gc { ptr: 0 };
    unsafe extern "C" fn init(rt: &mut RT) -> Gc {
        let num = make_gc_number(rt, 5.);
        send_actor(rt, FACT, num);
        let state = make_gc_number(rt, 1.);
        return state;
    }

    unsafe extern "C" fn update(rt: &mut RT, arg: Gc, state: Gc) -> Gc {
        rt.dump_frees();
        let stop_value = make_gc_string(
            rt,
            b"I am done with my work here\0" as *const [u8; 28] as *const i8,
        );

        let one_for_cmp = make_gc_number(rt, 1.);
        let one_for_minus = make_gc_number(rt, 1.);

        let le_res = eval_le(rt, arg, one_for_cmp);
        let cond_res = eval_conditional(rt, le_res);

        if cond_res == 1 {
            return stop_value;
        } else {
            let minused = eval_minus(rt, arg, one_for_minus);
            send_actor(rt, FACT, minused);
            let timesd = eval_mul(rt, arg, state);
            return timesd;
        }
    }

    #[test]
    fn start_test() {
        let init = init as *const u8;
        let update = update as *const u8;
        unsafe {
            FACT = make_actor_global(init, update);
        }

        unsafe {
            make_static(FACT);
        }

        unsafe { start_runtime() };
    }
}
