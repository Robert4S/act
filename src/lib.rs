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
    gc::{self, HeaderTag},
    runtime::{self, Pid},
};
static RT: LazyLock<Arc<RT>> = LazyLock::new(|| Arc::new(RT::new()));

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
pub extern "C" fn make_gc_number(rt: &RT) -> Gc {
    rt.make_gc(HeaderTag::Raw, 8)
}

#[no_mangle]
pub extern "C" fn make_gc_bool(rt: &RT) -> Gc {
    rt.make_gc(HeaderTag::Raw, 1)
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
    length_ptr.ptr::<usize>().write(length);
    let strdata = ActString {
        length: length_ptr,
        data,
    };
    write_str_to_buffer(data.ptr::<u8>(), s);
    let str_ptr = rt.make_gc(HeaderTag::TraceBlock, 16);
    str_ptr.ptr::<ActString>().write(strdata);
    str_ptr
}

#[no_mangle]
pub extern "C" fn eval_eq_bool(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    let b = unsafe { lhs.ptr::<u8>().read() == rhs.ptr::<u8>().read() };
    let ptr = make_gc_bool(runtime);
    unsafe {
        ptr.ptr::<u8>().write(b as u8);
    }
    ptr
}

#[no_mangle]
pub extern "C" fn eval_eq_num(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    let b = unsafe { lhs.ptr::<f64>().read() == rhs.ptr::<f64>().read() };
    let ptr = make_gc_bool(runtime);
    unsafe {
        ptr.ptr::<u8>().write(b as u8);
    }
    ptr
}

#[no_mangle]
pub extern "C" fn eval_eq_string(runtime: &RT, lhs: Gc, rhs: Gc) -> Gc {
    todo!();
    let b = unsafe { lhs.ptr::<f64>().read() == rhs.ptr::<f64>().read() };
    let ptr = make_gc_bool(runtime);
    unsafe {
        ptr.ptr::<u8>().write(b as u8);
    }
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
pub unsafe extern "C" fn print_number(_rt: &RT, number: Gc) {
    let num = number.ptr::<f64>().read();
    print!("{num}");
}

#[no_mangle]
pub unsafe extern "C" fn print_string(_rt: &RT, val: Gc) {
    let act_string = val.ptr::<ActString>().read();
    let s = act_string.to_str();
    print!("{s}");
}
