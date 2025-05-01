use core::slice;
use std::{
    alloc::{alloc, dealloc, Layout},
    collections::HashSet,
    mem,
};
const TAG_MASK: usize = 1;

pub fn mask_integer(value: i64) -> Gc {
    Gc((((value as usize) << 1) | TAG_MASK) as *mut u8)
}

pub fn unmask_integer(value: Gc) -> i64 {
    ((value.0 as usize) >> 1) as i64
}

pub fn unmask_pointer(value: Gc) -> *mut u8 {
    let p = value.0 as usize;
    (p & !TAG_MASK) as *mut u8
}

pub fn is_integer(value: Gc) -> bool {
    let p = value.0 as usize;
    (p & TAG_MASK) == TAG_MASK
}

use super::runtime::{Pid, RT};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Gc(pub *mut u8);

unsafe impl Send for Gc {}
unsafe impl Sync for Gc {}

impl Gc {
    pub fn ptr<T>(&self) -> *mut T {
        (unmask_pointer(*self)) as *mut T
    }

    pub unsafe fn is_eq(&self, other: Self) -> bool {
        if self.0 == other.0 {
            return true;
        }

        if is_integer(*self) {
            return false;
        }

        let header_ptr = self.ptr::<Header>();
        let header_ptr = header_ptr.sub(1);
        let own_h = header_ptr.read();
        let header_ptr = other.ptr::<Header>();
        let header_ptr = header_ptr.sub(1);
        let other_h = header_ptr.read();
        if own_h.size != other_h.size {
            return false;
        }
        match (own_h.tag, other_h.tag) {
            (HeaderTag::Raw, HeaderTag::Raw) => {
                let own_data = slice::from_raw_parts(self.0, own_h.size as usize);
                let other_data = slice::from_raw_parts(other.0, own_h.size as usize);
                own_data == other_data
            }
            (HeaderTag::TraceBlock, HeaderTag::TraceBlock) => {
                let size = own_h.size;
                let mut offset = 0;
                while offset < size {
                    let self_ptr = unsafe { self.0.add(offset as usize).into() };
                    let other_ptr = unsafe { other.0.add(offset as usize).into() };
                    if !Gc(self_ptr).is_eq(Gc(other_ptr)) {
                        return false;
                    }
                    offset += 8;
                }
                true
            }
            (HeaderTag::Pid, HeaderTag::Pid) => {
                let self_pid = self.ptr::<Pid>();
                let other_pid = other.ptr::<Pid>();
                self_pid.read() == other_pid.read()
            }
            _ => false,
        }
    }
}

impl From<*mut u8> for Gc {
    fn from(value: *mut u8) -> Self {
        Self(value)
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub enum HeaderTag {
    TraceBlock = 0,
    Raw = 1,
    Pid = 2,
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Header {
    tag: HeaderTag,
    size: u32,
}

impl Header {
    fn new(size: u32, tag: HeaderTag) -> Self {
        Self { size, tag }
    }
}

#[derive(Debug)]
pub struct Alloc {
    allocs: HashSet<Gc>,
    heap_limit: usize,
    heap_size: usize,
}

impl Default for Alloc {
    fn default() -> Self {
        Self {
            allocs: HashSet::new(),
            heap_limit: 4_000_000,
            heap_size: 0,
        }
    }
}

impl Alloc {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn update_heap_limit(&mut self, frac: f32, min_size: usize) {
        let new_limit = (self.heap_size as f64) * frac as f64;
        self.heap_limit = (new_limit.ceil() as usize).max(min_size);
    }

    pub fn heap_limit_reached(&self) -> bool {
        self.heap_size >= self.heap_limit
    }

    pub fn free_nonreachable(&mut self, reachable: &HashSet<Gc>) {
        let nonreachable = self
            .allocs
            .difference(&reachable)
            .cloned()
            .collect::<Vec<_>>();

        for p in nonreachable {
            self.free(p);
        }
    }

    pub fn alloc(&mut self, size: u32, tag: HeaderTag) -> Gc {
        let layout = Layout::from_size_align(mem::size_of::<Header>() + size as usize, 8).unwrap();
        let header = Header::new(size, tag);
        let data_ptr = unsafe {
            let header_ptr = alloc(layout) as *mut Header;
            header_ptr.write(header);
            header_ptr.add(1) as *mut u8
        };
        self.heap_size += size as usize;
        self.allocs.insert(data_ptr.into());
        data_ptr.into()
    }

    pub fn free(&mut self, data_ptr: Gc) {
        unsafe {
            let header_ptr = data_ptr.ptr::<Header>().sub(1);
            let size = header_ptr.read().size.clone();
            let layout =
                Layout::from_size_align(mem::size_of::<Header>() + size as usize, 8).unwrap();
            dealloc(header_ptr as *mut u8, layout);
            self.heap_size -= size as usize;
        }
    }

    pub fn mark(root: Gc, runtime: &RT, mark_set: &mut HashSet<Gc>) {
        if is_integer(root) {
            return;
        }
        if mark_set.contains(&root) {
            return;
        }
        mark_set.insert(root);
        let header = unsafe { root.ptr::<Header>().sub(1).read() };
        match header.tag {
            HeaderTag::TraceBlock => Self::trace_region(root, header.size, runtime, mark_set),
            HeaderTag::Raw => (),
            HeaderTag::Pid => {
                let pid_ptr = root.ptr::<Pid>();
                unsafe {
                    Self::mark_pid(pid_ptr.read(), runtime, mark_set);
                }
            }
        }
    }

    fn mark_pid(pid: Pid, runtime: &RT, mark_set: &mut HashSet<Gc>) {
        runtime.find_reachable_vals(&pid, mark_set);
    }

    fn trace_region(root: Gc, size: u32, runtime: &RT, mark_set: &mut HashSet<Gc>) {
        debug_assert!(
            size % 8 == 0,
            "A trace region must be the size of a whole number of 64 bit pointers"
        );
        let mut offset = 0;
        while offset < size {
            let ptr = unsafe { root.0.add(offset as usize).into() };
            Self::mark(ptr, runtime, mark_set);
            offset += 8;
        }
    }
}
