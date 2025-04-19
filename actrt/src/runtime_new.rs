use rayon::{current_num_threads, prelude::*};

use super::gc_new::{Allocator, Gc, Value};
use std::{
    collections::{HashMap, VecDeque},
    process::exit,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex,
    },
};

pub type Init = extern "C" fn(&RT) -> Gc;
pub type Update = extern "C" fn(&RT, Gc, Gc) -> Gc;

#[derive(Debug, Clone)]
enum ActorState {
    Uninit,
    Init(Gc),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Pid(pub usize);

#[derive(Debug, Clone)]
struct RTActor {
    init: Init,
    update: Update,
    state: ActorState,
}

impl RTActor {
    /// RTActors are lazily initialised. Calling new does not initialise their states with init(),
    /// it must be called separately and set
    pub fn new(init: Init, update: Update) -> Self {
        Self {
            init,
            update,
            state: ActorState::Uninit,
        }
    }

    /// Updating will call the updater with the state, and return an actor with the new the state if the output is
    /// normal. If the output signals that the actor is done, the return will be None
    pub fn update(&self, arg: Gc, runtime: &RT) -> Self {
        let state = self.ensure_init();
        let new_state = (self.update)(runtime, arg, state);
        Self {
            state: ActorState::Init(new_state),
            ..self.clone()
        }
    }

    fn ensure_init(&self) -> Gc {
        match self.state {
            ActorState::Uninit => panic!("Actor is unitialised upon call to ensure_init"),
            ActorState::Init(gc) => gc,
        }
    }

    fn initialise(&mut self, rt: &RT) {
        let new_state = (self.init)(rt);
        self.state = ActorState::Init(new_state);
    }
}

#[derive(Debug)]
struct Mailboxes {
    boxes: HashMap<Pid, VecDeque<Gc>>,
    queue: VecDeque<Pid>,
}

impl Mailboxes {
    fn push_message(&mut self, pid: Pid, val: Gc) {
        self.boxes.get_mut(&pid).unwrap().push_back(val);
        self.queue.push_back(pid);
    }

    fn pop_message(&mut self) -> Option<(Pid, Gc)> {
        let pid = self.queue.pop_front()?;
        let mailbox = self.boxes.get_mut(&pid).expect(&format!(
            "Holy guacamole pid {pid:?} is in the message queue but has no mailbox"
        ));
        let message = mailbox.pop_front()?;

        Some((pid, message))
    }

    fn add_pid(&mut self, pid: Pid) {
        self.boxes.insert(pid, VecDeque::new());
    }

    fn get_mailbox(&self, pid: Pid) -> Option<&VecDeque<Gc>> {
        self.boxes.get(&pid)
    }

    fn get_queue_deduped(&self) -> Vec<Pid> {
        let mut queue: Vec<Pid> = self.queue.iter().cloned().collect();
        queue.dedup();
        queue
    }

    fn is_empty(&self) -> bool {
        self.boxes.values().all(VecDeque::is_empty)
    }
}

impl Mailboxes {
    fn new() -> Self {
        Self {
            boxes: HashMap::new(),
            queue: VecDeque::new(),
        }
    }
}

#[derive(Debug)]
pub struct RT {
    mailboxes: Mutex<Mailboxes>,
    actors: Mutex<HashMap<Pid, RTActor>>,
    statics: Mutex<Vec<Gc>>,
    allocator: Mutex<Allocator>,
    pid_counter: AtomicUsize,
    epoch: AtomicUsize,
}

impl RT {
    pub fn new() -> Self {
        Self {
            mailboxes: Mutex::new(Mailboxes::new()),
            actors: Mutex::new(HashMap::new()),
            statics: Mutex::new(Vec::new()),
            allocator: Mutex::new(Allocator::new()),
            pid_counter: AtomicUsize::new(0),
            epoch: AtomicUsize::new(0),
        }
    }

    pub fn make_static(&self, value: Gc) -> () {
        self.statics.lock().unwrap().push(value);
    }

    pub fn make_actor(&self, init: Init, update: Update) -> Pid {
        let actor = RTActor::new(init, update);
        let pid = self.pid_counter.fetch_add(1, Ordering::SeqCst);
        let pid = Pid(pid);
        self.actors.lock().unwrap().insert(pid, actor);
        self.mailboxes.lock().unwrap().add_pid(pid);

        pid
    }

    pub fn make_gc(&self, value: Value) -> Gc {
        let ptr = self.allocator.lock().unwrap().alloc(value);
        Gc { ptr }
    }

    pub fn deref_gc(&self, ptr: &Gc) -> &Value {
        unsafe {
            let raw = self.allocator.lock().unwrap().get(ptr.ptr) as *const Value;
            &*raw
        }
    }

    pub fn init_actors(&self) {
        let mut actors = self.actors.lock().unwrap();
        let pids: Vec<Pid> = actors.keys().cloned().collect();

        for pid in pids {
            let actor = actors.get_mut(&pid).unwrap();
            actor.initialise(self);
        }
    }

    pub fn supervise(rt: Arc<Self>) {
        loop {
            let _ = rt.epoch.fetch_add(1, Ordering::SeqCst);

            let _new_states: Vec<Gc> = (0..current_num_threads().max(4))
                .filter_map(|_| rt.mailboxes.lock().unwrap().pop_message())
                .par_bridge()
                .into_par_iter()
                .map({
                    let rt_clone = rt.clone();
                    move |(pid, message)| rt_clone.update_actor(pid, message)
                })
                .collect();

            let reachable = rt.live_values();

            if rt.mailboxes.lock().unwrap().is_empty() {
                rt.destruct();
                exit(0);
            }

            rt.allocator.lock().unwrap().free_nonreachable(reachable);
        }
    }

    pub fn send_actor(&self, actor: Gc, value: Gc) {
        let actor = self.deref_gc(&actor).clone();

        match actor {
            Value::Pid(p) => {
                self.mailboxes.lock().unwrap().push_message(p, value);
            }
            other => panic!("{other:?} is not a PID"),
        }
    }

    pub fn find_reachable_vals(&self, pid: &Pid, marks: &mut Vec<Gc>) {
        let mailboxes = self.mailboxes.lock().unwrap();

        let mailbox = mailboxes.get_mailbox(pid.clone()).unwrap().clone();

        drop(mailboxes);

        for value in mailbox {
            value.mark(self, marks);
        }

        self.actor_state(pid).mark(self, marks);
    }
}

impl RT {
    fn destruct(&self) {
        let actors = self.actors.lock().unwrap();
        let states: Vec<(Pid, Value)> = actors
            .iter()
            .map(|(pid, actor)| (pid.clone(), self.deref_gc(&actor.ensure_init()).clone()))
            .collect();

        drop(actors);

        for (pid, final_state) in states {
            println!(
                "PID({}) finished with {}",
                pid.0,
                final_state.to_string(self)
            );
        }
    }

    fn update_actor(&self, pid: Pid, message: Gc) -> Gc {
        let actor = self.actors.lock().unwrap().get(&pid).unwrap().clone();
        let new_actor = actor.update(message, self);
        self.actors.lock().unwrap().insert(pid, new_actor.clone());
        new_actor.ensure_init()
    }

    pub fn dump_frees(&self) {
        println!("{:?}", self.allocator.lock().unwrap().free);
    }

    fn actor_state(&self, pid: &Pid) -> Gc {
        self.actors.lock().unwrap().get(pid).unwrap().ensure_init()
    }

    fn live_values(&self) -> Vec<Gc> {
        let statics = self.statics.lock().unwrap();
        let statics_clone = statics.clone();
        drop(statics);
        let mut marks = vec![];

        for static_var in statics_clone {
            static_var.mark(self, &mut marks);
        }

        let mailboxes = self.mailboxes.lock().unwrap();

        let nonempty: Vec<Pid> = mailboxes.get_queue_deduped();

        drop(mailboxes);

        for pid in nonempty {
            self.find_reachable_vals(&pid, &mut marks);
        }

        marks
    }
}
