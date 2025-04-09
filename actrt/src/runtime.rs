use core::fmt;
use std::{
    cell::RefCell,
    collections::HashMap,
    sync::{
        atomic::{AtomicUsize, Ordering},
        LazyLock, Mutex,
    },
};

use crate::gc::{Allocator, Gc};

pub static RUNTIME: LazyLock<Runtime> = LazyLock::new(|| Runtime {
    actors: Mutex::new(HashMap::new()),
    mailboxes: Mutex::new(HashMap::new()),
    pid_counter: AtomicUsize::new(0),
    allocator: Allocator::new(),
});

#[derive(Debug)]
pub struct Runtime {
    actors: Mutex<HashMap<Pid, RTActor>>,
    mailboxes: Mutex<HashMap<Pid, Vec<Gc>>>,
    pid_counter: AtomicUsize,
    pub allocator: Allocator,
}

impl Runtime {
    fn mark_actor(&self, pid: &Pid) -> Option<Vec<Gc>> {
        let actors = self.actors.lock().unwrap();
        let actor = actors.get(pid)?;
        let mut from_state = actor.state.borrow().mark();
        from_state.push(actor.state.borrow().clone());

        let mailboxes = self.mailboxes.lock().unwrap();
        let queue = mailboxes
            .get(pid)?
            .iter()
            .map(|p| p.mark())
            .flatten()
            .chain(from_state)
            .collect();

        Some(queue)
    }

    pub fn send_actor(&self, pid: Pid, value: Gc) {
        let mut mailboxes = self.mailboxes.lock().unwrap();
        mailboxes.get_mut(&pid).unwrap().push(value);
    }

    pub fn make_actor(
        &self,
        init: extern "C" fn() -> Gc,
        update: extern "C" fn(Gc, Gc) -> Gc,
    ) -> Pid {
        let actor = RTActor::new(init, update);
        let pid = self.pid_counter.fetch_add(1, Ordering::SeqCst);
        let mut actors = self.actors.lock().unwrap();
        actors.insert(Pid(pid), actor);
        Pid(pid)
    }
}

#[repr(C)]
pub struct RTActor {
    pub state: RefCell<Gc>,
    pub updater: extern "C" fn(Gc, Gc) -> Gc,
}

impl fmt::Debug for RTActor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RTActor")
            .field("state", &self.state)
            .finish()
    }
}

impl RTActor {
    fn new(init: extern "C" fn() -> Gc, updater: extern "C" fn(Gc, Gc) -> Gc) -> Self {
        let state = init();
        Self {
            state: RefCell::new(state),
            updater,
        }
    }

    fn update(&self, message: Gc) {
        let new_state = (self.updater)(message, self.state.borrow().clone());
        *self.state.borrow_mut() = new_state;
    }
}

unsafe impl Sync for RTActor {}
unsafe impl Send for RTActor {}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Pid(usize);
impl Pid {
    pub fn mark(&self) -> Vec<Gc> {
        RUNTIME.mark_actor(self).unwrap()
    }
}
