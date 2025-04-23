use std::{
    alloc::{alloc, dealloc, Layout},
    collections::HashSet,
    mem,
};

use super::runtime::{Pid, RT};

#[repr(transparent)]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Gc(*mut u8);

unsafe impl Send for Gc {}
unsafe impl Sync for Gc {}

impl Gc {
    pub fn ptr<T>(&self) -> *mut T {
        self.0 as *mut T
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
            heap_limit: 1e6 as usize,
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
        if !self.allocs.remove(&data_ptr) {
            panic!("Allocation {data_ptr:?} doesnt exist");
        }
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
        assert!(
            size % 8 == 0,
            "A trace region must be the size of a whole number of 64 bit pointers"
        );
        let mut offset = 0;
        while offset < size {
            unsafe {
                Self::mark(root.0.add(offset as usize).into(), runtime, mark_set);
            }
            offset += 8;
        }
    }

    fn dump(&self) {
        dbg!(&self.allocs);
    }
}
