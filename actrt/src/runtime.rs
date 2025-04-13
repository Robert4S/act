use core::fmt;
use std::{
    collections::{HashMap, VecDeque},
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc, Mutex, Once, RwLock,
    },
    thread::{self, yield_now, JoinHandle},
};

use crate::gc::{Allocator, Gc, Value};

pub fn get_runtime() -> &'static Runtime {
    unsafe {
        INIT.call_once(|| {
            let r = Runtime {
                actors: Mutex::new(Actors {
                    actors: HashMap::new(),
                    mailboxes: HashMap::new(),
                }),
                states: Mutex::new(HashMap::new()),
                pid_counter: AtomicUsize::new(0),
                allocator: Allocator::new(),
                handlers: Mutex::new(vec![]),
                runtime_started: AtomicBool::new(false),
                statics: Mutex::new(Vec::new()),
                should_stop: Arc::new(RwLock::new(())),
                static_vars: Mutex::new(vec![]),
            };
            RUNTIME = Some(r);
        });
    }

    unsafe { RUNTIME.as_ref().expect("RUNTIME not initialised") }
}

static mut RUNTIME: Option<Runtime> = None;

static INIT: Once = Once::new();

#[derive(Debug)]
struct Actors {
    mailboxes: HashMap<Pid, VecDeque<Gc>>,
    actors: HashMap<Pid, RTActor>,
}

#[derive(Debug)]
pub struct Runtime {
    actors: Mutex<Actors>,
    pid_counter: AtomicUsize,
    pub allocator: Allocator,
    handlers: Mutex<Vec<JoinHandle<()>>>,
    runtime_started: AtomicBool,
    states: Mutex<HashMap<Pid, Gc>>,
    statics: Mutex<Vec<Pid>>,
    should_stop: Arc<RwLock<()>>,
    static_vars: Mutex<Vec<Gc>>,
}

impl Runtime {
    pub fn make_static(&self, value: Gc) -> () {
        self.static_vars.lock().unwrap().push(value);
    }

    pub fn mark_and_sweep(&self, roots: Vec<Gc>) -> () {
        self.allocator.mark_and_sweep(roots);
    }

    pub fn send_actor(&self, pid: Pid, value: Gc) {
        let mut mailboxes = self.actors().lock().unwrap();
        let mailboxes = mailboxes.mailboxes.get_mut(&pid).unwrap();
        mailboxes.push_back(value);
    }

    pub fn make_actor(
        &self,
        init: extern "C" fn() -> Gc,
        update: extern "C" fn(Gc, Gc) -> Gc,
    ) -> Pid {
        let actor = RTActor::new(init, update);
        let pid = self.pid_counter.fetch_add(1, Ordering::SeqCst);
        let mut actors = self.actors().lock().unwrap();
        actors.actors.insert(Pid(pid), actor);
        actors.mailboxes.insert(Pid(pid), VecDeque::new());
        self.states.lock().unwrap().insert(
            Pid(pid),
            Gc::new(Value::Undefined(format!("From actor creation"))),
        );
        if self.runtime_started.load(Ordering::SeqCst) {
            let should_stop = self.should_stop.clone();
            self.handlers
                .lock()
                .unwrap()
                .push(thread::spawn(move || run_actor(Pid(pid), should_stop)));
        }
        Pid(pid)
    }

    pub fn start_runtime(&self) -> () {
        let pids = self
            .actors
            .lock()
            .unwrap()
            .actors
            .keys()
            .cloned()
            .collect::<Vec<Pid>>();

        *self.statics.lock().unwrap() = pids.clone();

        let mut handlers = Vec::new();

        for p in pids {
            let should_stop = self.should_stop.clone();
            handlers.push(thread::spawn(move || run_actor(p.clone(), should_stop)));
        }

        *self.handlers.lock().unwrap() = handlers;

        self.supervise(self.should_stop.clone())
    }
}

impl Runtime {
    fn get_state(&self, pid: &Pid) -> Option<Gc> {
        self.states.lock().unwrap().get(pid).cloned()
    }

    fn actors(&self) -> &Mutex<Actors> {
        &self.actors
    }

    fn set_state(&self, pid: Pid, state: Gc) -> () {
        let _ = self.states.lock().unwrap().insert(pid, state);
    }

    fn mark_actor(&self, pid: &Pid, state: Gc) -> Option<Vec<Gc>> {
        let actors = self.actors().lock().unwrap();
        let mut from_state = state.mark();
        from_state.push(state);

        let queue = actors
            .mailboxes
            .get(pid)?
            .iter()
            .map(|p| p.mark())
            .flatten()
            .chain(from_state)
            .collect();

        Some(queue)
    }

    fn update_actor(&self, pid: &Pid, state: Gc) -> Option<Gc> {
        let (actor, message): (RTActor, Gc) = {
            let mut actors = self.actors().lock().unwrap();
            let mailbox = actors.mailboxes.get_mut(pid)?;
            let message = mailbox.pop_front()?;
            let actor = actors
                .actors
                .get(pid)
                .expect("Mailbox exists, but actor does not");

            (actor.clone(), message)
        };
        Some(actor.update(message, state))
    }

    fn supervise(&self, should_stop: Arc<RwLock<()>>) -> () {
        let mut acc = 0_usize;
        loop {
            acc = acc.wrapping_add(1);
            let mut handlers = self.handlers.lock().unwrap();
            let finished = handlers
                .iter()
                .enumerate()
                .filter(|(_, h)| h.is_finished())
                .map(|(i, _)| i)
                .collect::<Vec<usize>>();

            for i in finished {
                handlers.remove(i);
            }

            if handlers.len() == 0 {
                break;
            }

            let lock = should_stop.write().unwrap();
            self.start_gc();
            drop(lock);
        }
    }

    fn start_gc(&self) -> () {
        let roots = {
            let statics = self.statics.lock().unwrap();
            let static_vars = self.static_vars.lock().unwrap();
            let mailboxes = &self.actors().lock().unwrap().mailboxes;
            let static_roots = statics.iter().map(|a| self.get_state(a).unwrap());

            let static_var_roots = static_vars.iter().cloned();

            let mailbox_roots = mailboxes
                .values()
                .filter(|m| !m.is_empty())
                .flatten()
                .cloned();

            static_roots
                .chain(mailbox_roots)
                .chain(static_var_roots)
                .collect()
        };

        self.allocator.mark_and_sweep(roots);
    }
}

fn run_actor(pid: Pid, should_stop: Arc<RwLock<()>>) -> () {
    let mut init = None;
    {
        let lock = should_stop.read().unwrap();
        init = Some(get_runtime().actors.lock().unwrap().actors[&pid].init);
        drop(lock);
    }
    let mut current_state = (init.unwrap())();
    loop {
        let lock = should_stop.read().unwrap();
        match get_runtime().update_actor(&pid, current_state) {
            None => continue,
            Some(gc) => {
                let v: &Value = &gc;
                if let Value::String(s) = v {
                    if s == "I am done with my work here" {
                        let current_state: &Value = &current_state;
                        println!("{pid:?} finished with {current_state:?}");
                        break;
                    }
                }
                current_state = gc;
                get_runtime().set_state(pid, current_state);
            }
        }
        drop(lock);
    }
}

#[repr(C)]
#[derive(Clone)]
pub struct RTActor {
    pub updater: extern "C" fn(Gc, Gc) -> Gc,
    pub init: extern "C" fn() -> Gc,
}

impl fmt::Debug for RTActor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RTActor").field("state", &0_usize).finish()
    }
}

impl RTActor {
    fn new(init: extern "C" fn() -> Gc, updater: extern "C" fn(Gc, Gc) -> Gc) -> Self {
        Self { updater, init }
    }

    fn update(&self, message: Gc, state: Gc) -> Gc {
        let new_state = (self.updater)(message, state);
        new_state
    }
}

unsafe impl Sync for RTActor {}
unsafe impl Send for RTActor {}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Pid(usize);
impl Pid {
    pub fn mark(&self) -> Vec<Gc> {
        let runtime = get_runtime();
        let state = runtime.get_state(self).unwrap();
        runtime.mark_actor(self, state).unwrap()
    }
}
