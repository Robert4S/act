use rayon::{current_num_threads, prelude::*};

use super::gc::{Alloc, Gc, HeaderTag};
use parking_lot::Mutex;
use std::{
    collections::{BTreeSet, HashMap, HashSet, VecDeque},
    process::exit,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};

pub type Init = extern "C" fn(&RT) -> Gc;
pub type Update = extern "C" fn(&RT, Gc, Gc) -> Gc;

#[derive(Debug, Clone)]
enum ActorState {
    Uninit,
    Init(Gc),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
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
        debug_assert!(matches!(self.state, ActorState::Init(_)));
        if let ActorState::Init(gc) = self.state {
            gc
        } else {
            unsafe { std::hint::unreachable_unchecked() }
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
    fn new() -> Self {
        Self {
            boxes: HashMap::new(),
            queue: VecDeque::new(),
        }
    }

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

    fn pop_messages(&mut self, num: usize) -> Vec<(Pid, Gc)> {
        let mut already_popped = BTreeSet::new();
        let mut reinsert = Vec::new();
        let mut popped = Vec::new();

        while popped.len() <= num {
            if let Some((pid, message)) = self.pop_message() {
                if already_popped.contains(&pid) {
                    reinsert.push((pid, message));
                } else {
                    popped.push((pid, message));
                    already_popped.insert(pid);
                }
            } else {
                break;
            }
        }

        while let Some((pid, message)) = reinsert.pop() {
            self.push_message(pid, message);
        }

        popped
    }
}

#[derive(Debug)]
pub struct RT {
    mailboxes: Mutex<Mailboxes>,
    actors: Mutex<HashMap<Pid, RTActor>>,
    statics: Mutex<Vec<Gc>>,
    allocator: Mutex<Alloc>,
    pid_counter: AtomicUsize,
    epoch: AtomicUsize,
}

impl RT {
    pub fn new() -> Self {
        Self {
            mailboxes: Mutex::new(Mailboxes::new()),
            actors: Mutex::new(HashMap::new()),
            statics: Mutex::new(Vec::new()),
            allocator: Mutex::new(Alloc::new()),
            pid_counter: AtomicUsize::new(0),
            epoch: AtomicUsize::new(0),
        }
    }

    pub fn make_static(&self, value: Gc) -> () {
        self.statics.lock().push(value);
    }

    pub fn make_actor(&self, init: Init, update: Update) -> Pid {
        let actor = RTActor::new(init, update);
        let pid = self.pid_counter.fetch_add(1, Ordering::SeqCst);
        let pid = Pid(pid);
        self.actors.lock().insert(pid, actor);
        self.mailboxes.lock().add_pid(pid);

        pid
    }

    pub fn make_gc(&self, tag: HeaderTag, size: u32) -> Gc {
        self.allocator.lock().alloc(size, tag)
    }

    pub fn init_actors(&self) {
        let mut actors = self.actors.lock();
        let pids: Vec<Pid> = actors.keys().cloned().collect();

        for pid in pids {
            let actor = actors.get_mut(&pid).unwrap();
            actor.initialise(self);
        }
    }

    pub fn supervise(rt: Arc<Self>) {
        let mut set = HashSet::new();
        loop {
            let e = rt.epoch.fetch_add(1, Ordering::SeqCst);

            // TODO: Make sure an actor does not get more than one message to respond to in each
            // scheduling epoch
            let mut mailboxes = rt.mailboxes.lock();
            let messages = mailboxes.pop_messages(current_num_threads());

            drop(mailboxes);

            let _new_states: Vec<Gc> = messages
                .into_par_iter()
                .map({
                    let rt_clone = rt.clone();
                    move |(pid, message)| rt_clone.update_actor(pid, message)
                })
                .collect();

            unsafe {
                if rt.allocator.make_guard_unchecked().heap_limit_reached() {
                    rt.live_values(&mut set);
                    rt.allocator.lock().free_nonreachable(&set);
                    set.clear();
                    rt.allocator
                        .make_guard_unchecked()
                        .update_heap_limit(2., 1e6 as usize);
                }
                if rt.mailboxes.make_guard_unchecked().is_empty() {
                    rt.destruct();
                    exit(0);
                }
            }
        }
    }

    pub fn send_actor(&self, actor: Gc, value: Gc) {
        let actor = unsafe { actor.ptr::<Pid>().read() };
        self.mailboxes.lock().push_message(actor, value);
    }

    pub fn find_reachable_vals(&self, pid: &Pid, marks: &mut HashSet<Gc>) {
        let mailboxes = self.mailboxes.lock();

        let mailbox = unsafe {
            mailboxes
                .get_mailbox(pid.clone())
                .unwrap_unchecked()
                .clone()
        };

        drop(mailboxes);

        for value in mailbox {
            Alloc::mark(value, self, marks);
        }

        let state = self.actor_state(pid);
        Alloc::mark(state, self, marks);
    }
}

impl RT {
    fn destruct(&self) {
        ()
    }

    fn update_actor(&self, pid: Pid, message: Gc) -> Gc {
        let actor = unsafe { self.actors.lock().get(&pid).unwrap_unchecked().clone() };
        let new_actor = actor.update(message, self);
        self.actors.lock().insert(pid, new_actor.clone());
        new_actor.ensure_init()
    }

    fn actor_state(&self, pid: &Pid) -> Gc {
        unsafe { self.actors.lock().get(pid).unwrap_unchecked().ensure_init() }
    }

    fn live_values(&self, marks: &mut HashSet<Gc>) {
        let statics = self.statics.lock();
        let statics_clone = statics.clone();
        drop(statics);

        for static_var in statics_clone {
            Alloc::mark(static_var, self, marks);
        }

        let mailboxes = self.mailboxes.lock();

        let nonempty: Vec<Pid> = mailboxes.get_queue_deduped();

        drop(mailboxes);

        for pid in nonempty {
            self.find_reachable_vals(&pid, marks);
        }
    }
}
