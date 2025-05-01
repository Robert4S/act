use core::{slice, str};
use std::{
    ffi::CStr,
    ptr,
    sync::{Arc, LazyLock},
};

use gc::Gc;
use runtime::RT;

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

mod runtimelib;

use runtimelib::{
    gc::{self, mask_integer, unmask_integer, HeaderTag},
    runtime::{self, Pid},
};
static RT: LazyLock<Arc<RT>> = LazyLock::new(|| Arc::new(RT::new()));

#[no_mangle]
pub extern "C" fn eq_val(rt: &RT, v1: Gc, v2: Gc) -> Gc {
    let b = unsafe { v1.is_eq(v2) };
    make_gc_bool(rt, b)
}

#[no_mangle]
pub extern "C" fn make_actor(
    rt: &RT,
    init: extern "C" fn(&RT) -> Gc,
    update: extern "C" fn(&RT, Gc, Gc) -> Gc,
) -> Gc {
    let actor = rt.make_actor(init, update);
    let actor_ptr = rt.make_gc(HeaderTag::Pid, 8);
    unsafe {
        actor_ptr.ptr::<Pid>().write(actor);
    }
    actor_ptr
}

#[no_mangle]
pub extern "C" fn make_gc_unit(rt: &RT) -> Gc {
    rt.make_gc(HeaderTag::Raw, 0)
}

#[no_mangle]
pub extern "C" fn make_actor_global(
    init: extern "C" fn(&RT) -> Gc,
    update: extern "C" fn(&RT, Gc, Gc) -> Gc,
    slot: *mut Gc,
) {
    let gc = make_actor(&RT, init, update);
    unsafe {
        slot.write(gc);
        RT.make_static(gc);
    }
}

#[no_mangle]
pub extern "C" fn make_gc_int(_rt: &RT, n: i64) -> Gc {
    let res = gc::mask_integer(n);
    res
}

#[no_mangle]
pub extern "C" fn unmask_int(_rt: &RT, n: Gc) -> i64 {
    gc::unmask_integer(n)
}

#[no_mangle]
pub extern "C" fn make_gc_float(rt: &RT) -> Gc {
    rt.make_gc(HeaderTag::Raw, 8)
}

#[no_mangle]
pub extern "C" fn make_gc_bool(_rt: &RT, b: bool) -> Gc {
    mask_integer(b as i64)
}

#[repr(C)]
struct ActString {
    length: Gc,
    data: Gc,
}

impl ActString {
    fn from_str(buffer: Gc, length: Gc, str: &str) -> Self {
        unsafe {
            length.ptr::<usize>().write(str.len());
        }
        write_str_to_buffer(buffer.ptr(), str);
        Self {
            length,
            data: buffer,
        }
    }

    fn to_str(&self) -> &str {
        let slice = unsafe {
            slice::from_raw_parts(self.data.ptr::<u8>(), self.length.ptr::<usize>().read())
        };
        str::from_utf8(slice).unwrap()
    }
}

fn write_str_to_buffer(buffer: *mut u8, input: &str) {
    // Convert the &str to bytes
    let bytes = input.as_bytes();
    let len = bytes.len();

    unsafe {
        // Copy the bytes to the buffer
        ptr::copy_nonoverlapping(bytes.as_ptr(), buffer, len);
    }
}

#[no_mangle]
pub unsafe extern "C" fn make_gc_string(rt: &RT, string: *const i8) -> Gc {
    let s = CStr::from_ptr(string).to_str().unwrap();
    let length = s.len();
    let data = rt.make_gc(HeaderTag::Raw, length as u32);
    let length_ptr = rt.make_gc(HeaderTag::Raw, 8);
    let strdata = ActString::from_str(data, length_ptr, s);
    let str_ptr = rt.make_gc(HeaderTag::TraceBlock, 16);
    str_ptr.ptr::<ActString>().write(strdata);
    str_ptr
}

#[no_mangle]
pub extern "C" fn eval_eq_bool(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    eval_eq_int(runtime, lhs, rhs)
}

#[no_mangle]
pub extern "C" fn eval_eq_float(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    let b = unsafe { lhs.ptr::<f64>().read() == rhs.ptr::<f64>().read() };
    let ptr = make_gc_bool(runtime, b);

    ptr
}

#[no_mangle]
pub extern "C" fn eval_eq_int(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    let b = unmask_integer(lhs) == unmask_integer(rhs);
    let ptr = make_gc_bool(runtime, b);
    ptr
}

#[no_mangle]
pub extern "C" fn eval_eq_string(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    let b = unsafe { lhs.ptr::<ActString>().read().to_str() }
        == unsafe { rhs.ptr::<ActString>().read().to_str() };
    let ptr = make_gc_bool(runtime, b);

    ptr
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
pub unsafe extern "C" fn print_newline(_rt: &RT) {
    println!()
}

#[no_mangle]
pub unsafe extern "C" fn print_int(_rt: &RT, number: Gc) {
    let num = unmask_integer(number);
    println!("{num}");
}

#[no_mangle]
pub unsafe extern "C" fn print_float(_rt: &RT, number: Gc) {
    let num = number.ptr::<f64>().read();
    println!("{num}");
}

#[no_mangle]
pub unsafe extern "C" fn eval_int_div(_rt: &RT, left: i64, right: i64) -> Gc {
    let res = left / right;
    mask_integer(res)
}

#[no_mangle]
pub unsafe extern "C" fn print_string(_rt: &RT, val: Gc) {
    let act_string = val.ptr::<ActString>().read();
    let s = act_string.to_str();
    print!("{s}");
}

#[no_mangle]
pub unsafe extern "C" fn alloc_record(rt: &RT, size: u32) -> Gc {
    let gc = rt.make_gc(HeaderTag::TraceBlock, size);
    std::ptr::write_bytes(gc.ptr::<u8>(), 0, size as usize);
    gc
}
