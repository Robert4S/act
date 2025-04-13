use crate::get_rt;

use super::gc::{Allocator, Gc, Value};
use std::{
    collections::{HashMap, VecDeque},
    sync::{Arc, Mutex},
    thread::{self, yield_now, JoinHandle},
};

enum GcResult {
    EmptyMailbox,
    #[allow(unused)]
    Updated(Gc),
}

pub type Init = extern "C" fn(&mut RT) -> Gc;
pub type Update = extern "C" fn(&mut RT, Gc, Gc) -> Gc;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Pid(usize);

#[derive(Debug, Clone)]
struct RTActor {
    init: Init,
    update: Update,
    state: Gc,
}

impl RTActor {
    /// RTActors are lazily initialised. Calling new does not initialise their states with init(),
    /// it must be called separately and set
    pub fn new(init: Init, update: Update, runtime: &mut RT) -> Self {
        Self {
            init,
            update,
            state: runtime.make_gc(Value::Undefined(String::from("From actor creation"))),
        }
    }

    /// Updating will call the updater with the state, and return an actor with the new the state if the output is
    /// normal. If the output signals that the actor is done, the return will be None
    pub fn update(&self, arg: Gc, runtime: &mut RT) -> Option<Self> {
        let arg_v = runtime.deref_gc(&arg);
        if let Value::Bool(_) = arg_v {
            panic!("Fuck you");
        }
        let new_state = (self.update)(runtime, arg, self.state);
        match runtime.deref_gc(&new_state) {
            Value::String(s) if s.as_str() == "I am done with my work here" => None,
            _ => Some(Self {
                state: new_state,
                ..self.clone()
            }),
        }
    }
}

#[derive(Debug)]
pub struct RT {
    mailboxes: HashMap<Pid, VecDeque<Gc>>,
    actors: HashMap<Pid, RTActor>,
    statics: Vec<Gc>,
    started: bool,
    allocator: Allocator,
    pid_counter: usize,
    handlers: HashMap<Pid, JoinHandle<()>>,
}

impl RT {
    pub fn new() -> Self {
        Self {
            mailboxes: HashMap::new(),
            actors: HashMap::new(),
            statics: Vec::new(),
            started: false,
            allocator: Allocator::new(),
            pid_counter: 0,
            handlers: HashMap::new(),
        }
    }

    pub fn make_static(&mut self, value: Gc) -> () {
        self.statics.push(value);
    }

    /// If the runtime has been started, this will immediately spawn a thread to "run" the actor.
    /// If not, the actor will be started once the runtime is started
    pub fn make_actor(&mut self, rt: &'static Arc<Mutex<RT>>, init: Init, update: Update) -> Pid {
        let actor = RTActor::new(init, update, self);
        self.pid_counter += 1;
        let pid = Pid(self.pid_counter);
        self.actors.insert(pid, actor);
        self.mailboxes.insert(pid, VecDeque::new());

        if self.started {
            self.start_actor(rt, pid);
        }

        pid
    }

    pub fn make_gc(&mut self, value: Value) -> Gc {
        let ptr = self.allocator.alloc(value);
        Gc { ptr }
    }

    pub fn mark_actor(&self, pid: &Pid) -> Vec<Gc> {
        let state = self.actors.get(pid).unwrap().state;
        let mut from_state = state.mark(self);

        let mailbox = self.mailboxes.get(pid).unwrap();
        let mut from_mailbox: Vec<_> = mailbox
            .into_iter()
            .map(|v| v.mark(self))
            .flatten()
            .collect();

        from_state.append(&mut from_mailbox);

        from_state
    }

    pub fn start_actor(&mut self, rt: &'static Arc<Mutex<RT>>, pid: Pid) -> () {
        let handler = thread::spawn(move || Self::run_actor(pid, &rt));
        self.handlers.insert(pid, handler);
    }

    pub fn start_runtime(rt: &'static Arc<Mutex<RT>>) -> () {
        let mut lock = rt.lock().unwrap();
        let keys = lock.actors.keys().cloned().collect::<Vec<Pid>>();

        for k in keys {
            lock.start_actor(rt, k);
        }

        lock.started = true;
    }

    pub fn deref_gc(&self, ptr: &Gc) -> &Value {
        unsafe { self.allocator.get(ptr.ptr) }
    }

    pub fn supervise(with_gc: bool) {
        let mut acc: usize = 0;
        loop {
            acc = acc.wrapping_add(1);
            if acc % 8 != 0 {
                yield_now();
                continue;
            }
            let rt = get_rt();
            if rt.lock().unwrap().is_finished() {
                break;
            }
            if acc % 16 == 0 && with_gc {
                rt.lock().unwrap().run_gc();
            }
        }
    }

    pub fn send_actor(&mut self, actor: Gc, value: Gc) {
        let actor = self.deref_gc(&actor).clone();

        match actor {
            Value::Pid(p) => {
                self.mailboxes.get_mut(&p).unwrap().push_back(value);
            }
            other => panic!("{other:?} is not a PID"),
        }
    }
}

impl RT {
    fn run_actor(pid: Pid, rt: &'static Arc<Mutex<RT>>) {
        let mut lock = rt.lock().unwrap();
        lock.init_actor(pid);
        drop(lock);
        loop {
            // VERY IMPORTANT: You cannot lock the world without having a lock on the runtime,
            // because if you do not have a lock on the runtime, the garbage collecter may get one.
            // This will result in a deadlock where the GC has the runtime and wants to stop the
            // world, but a read lock is held on the world here, and will not be released because
            // it is waiting for a lock on the runtime.
            let mut rt_lock = rt.lock().unwrap();
            match rt_lock.update_actor(pid) {
                None => break,
                Some(GcResult::EmptyMailbox) => (),
                Some(GcResult::Updated(_)) => continue,
            }
            drop(rt_lock);
        }
    }

    fn init_actor(&mut self, pid: Pid) {
        let actor = self.actors.get(&pid).unwrap().clone();
        let state = (actor.init)(self);
        let new_actor = RTActor {
            state,
            ..actor.clone()
        };
        self.actors.insert(pid, new_actor);
    }

    fn live_values(&mut self, roots: Vec<Gc>) -> Vec<usize> {
        let t = roots.clone();
        let root_values = t
            .iter()
            .map(|ptr| self.deref_gc(ptr))
            .cloned()
            .collect::<Vec<_>>();

        let mut marks = vec![];
        for v in root_values {
            marks.push(v.mark(self));
        }

        let mut marks = marks
            .into_iter()
            .flatten()
            .map(|p| p.ptr)
            .chain(roots.iter().map(|p| p.ptr))
            .collect::<Vec<usize>>();

        marks.dedup();

        marks
    }

    fn update_actor(&mut self, pid: Pid) -> Option<GcResult> {
        let actor = self.actors.get(&pid).unwrap().clone();
        let message = self.mailboxes.get_mut(&pid).unwrap().pop_front();
        match message {
            Some(v) => {
                let new_actor = actor.update(v, self)?;
                self.actors.insert(pid, new_actor.clone());
                Some(GcResult::Updated(new_actor.state))
            }
            None => Some(GcResult::EmptyMailbox),
        }
    }

    pub fn dump_frees(&self) {
        println!("{:?}", self.allocator.free);
    }

    fn mark_and_sweep(&mut self, roots: Vec<Gc>) {
        let marks = self.live_values(roots);

        let not_marked = {
            (0..(self.allocator.values.len() - 1))
                .filter(|key| !marks.contains(key))
                .collect::<Vec<usize>>()
        };

        unsafe { self.allocator.sweep(not_marked) }
    }

    fn actor_state(&self, pid: &Pid) -> Gc {
        self.actors.get(pid).unwrap().state.clone()
    }

    fn is_finished(&self) -> bool {
        self.handlers
            .iter()
            .filter_map(|(pid, handle)| {
                if handle.is_finished() {
                    println!(
                        "Pid {} finished with {:?}",
                        pid.0,
                        self.deref_gc(&self.actor_state(pid))
                    );
                    None
                } else {
                    Some(pid)
                }
            })
            .next()
            .is_none()
    }

    fn run_gc(&mut self) {
        let static_roots = self.statics.iter().cloned();
        let mailbox_roots = self
            .mailboxes
            .values()
            .filter(|v| !v.is_empty())
            .flatten()
            .cloned();

        let mut roots: Vec<Gc> = static_roots.chain(mailbox_roots).collect();

        roots.dedup();

        self.mark_and_sweep(roots);
    }
}
