mod gc;
mod runtime;

pub type RT = runtime::RT;
pub type Gc = gc::Gc;
pub type Value = gc::Value;
pub type Init = runtime::Init;
pub type Update = runtime::Update;
