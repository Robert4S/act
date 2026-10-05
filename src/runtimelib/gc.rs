use core::slice;
use std::{
    alloc::{alloc, dealloc, Layout},
    collections::HashSet,
    hash::{BuildHasherDefault, Hasher},
    mem,
};
const TAG_MASK: usize = 1;

/// Blocks with payloads up to this many bytes are recycled through per-size free lists
/// instead of being returned to the system allocator.
const POOLED_MAX: usize = 128;
const POOL_CAPACITY: usize = 1 << 16;

/// Hashes GC pointers by multiplication; they are already well distributed and SipHash
/// dominated collection time.
#[derive(Default)]
pub struct PtrHasher(u64);

impl Hasher for PtrHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0.rotate_left(8) ^ *b as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
    }

    fn write_usize(&mut self, n: usize) {
        self.0 = (n as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15).rotate_left(29);
    }
}

pub type MarkSet = HashSet<Gc, BuildHasherDefault<PtrHasher>>;

pub fn mask_integer(value: i64) -> Gc {
    Gc((((value as usize) << 1) | TAG_MASK) as *mut u8)
}

pub fn unmask_integer(value: Gc) -> i64 {
    (value.0 as i64) >> 1
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
                    let self_field = (self.0.add(offset as usize) as *const Gc).read();
                    let other_field = (other.0.add(offset as usize) as *const Gc).read();
                    if !self_field.is_eq(other_field) {
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
    allocs: Vec<Gc>,
    pools: Vec<Vec<*mut Header>>,
    heap_limit: usize,
    heap_size: usize,
}

unsafe impl Send for Alloc {}

impl Default for Alloc {
    fn default() -> Self {
        Self {
            allocs: Vec::new(),
            pools: (0..=POOLED_MAX / 8).map(|_| Vec::new()).collect(),
            heap_limit: 4_000_000,
            heap_size: 0,
        }
    }
}

fn block_layout(size: u32) -> Layout {
    let payload = (size as usize + 7) & !7;
    Layout::from_size_align(mem::size_of::<Header>() + payload, 8).unwrap()
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

    pub fn free_nonreachable(&mut self, reachable: &MarkSet) {
        let mut allocs = mem::take(&mut self.allocs);
        allocs.retain(|p| {
            let live = reachable.contains(p);
            if !live {
                self.free(*p);
            }
            live
        });
        self.allocs = allocs;
    }

    pub fn alloc(&mut self, size: u32, tag: HeaderTag) -> Gc {
        let header = Header::new(size, tag);
        let class = (size as usize + 7) / 8;
        let recycled = self.pools.get_mut(class).and_then(Vec::pop);
        let data_ptr = unsafe {
            let header_ptr = recycled.unwrap_or_else(|| alloc(block_layout(size)) as *mut Header);
            header_ptr.write(header);
            header_ptr.add(1) as *mut u8
        };
        self.heap_size += size as usize;
        self.allocs.push(data_ptr.into());
        data_ptr.into()
    }

    pub fn free(&mut self, data_ptr: Gc) {
        unsafe {
            let header_ptr = data_ptr.ptr::<Header>().sub(1);
            let size = header_ptr.read().size;
            self.heap_size -= size as usize;
            let class = (size as usize + 7) / 8;
            match self.pools.get_mut(class) {
                Some(pool) if pool.len() < POOL_CAPACITY => pool.push(header_ptr),
                _ => dealloc(header_ptr as *mut u8, block_layout(size)),
            }
        }
    }

    pub fn mark(root: Gc, runtime: &RT, mark_set: &mut MarkSet) {
        if is_integer(root) || root.0.is_null() {
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

    fn mark_pid(pid: Pid, runtime: &RT, mark_set: &mut MarkSet) {
        runtime.find_reachable_vals(&pid, mark_set);
    }

    fn trace_region(root: Gc, size: u32, runtime: &RT, mark_set: &mut MarkSet) {
        debug_assert!(
            size % 8 == 0,
            "A trace region must be the size of a whole number of 64 bit pointers"
        );
        let mut offset = 0;
        while offset < size {
            let field = unsafe { (root.0.add(offset as usize) as *const Gc).read() };
            Self::mark(field, runtime, mark_set);
            offset += 8;
        }
    }
}
