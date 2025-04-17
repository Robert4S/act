use core::fmt;
use std::{collections::HashMap, iter};

type EmitError = String;
type Result<T> = core::result::Result<T, EmitError>;

fn merge<K: Clone, V: Clone>(map1: &mut HashMap<K, V>, map2: &HashMap<K, V>) -> ()
where
    K: Eq + std::hash::Hash,
{
    for (k, v) in map2 {
        map1.entry(k.clone()).or_insert(v.clone()); // inserts only if key is not already present
    }
}

#[derive(Clone)]
pub struct Update {
    pub arg: String,
    pub body: Vec<Instruction>,
}

#[derive(Clone)]
pub struct Init {
    pub body: Vec<Instruction>,
}

#[derive(Clone)]
pub struct Actor {
    pub name: String,
    pub state_name: String,
    pub update: Update,
    pub init: Init,
}

#[derive(Clone)]
pub enum Instruction {
    Assignment {
        name: String,
        value: Value,
    },
    Send {
        to: Value,
        value: Value,
    },
    Actor(Actor),
    Daemon(Actor),
    Return(Value),
    If {
        cond: Value,
        then: Vec<Instruction>,
        otherwise: Vec<Instruction>,
    },
}

fn align_call() -> String {
    format!("and $0xFFFFFFFFFFFFFFF0, %rsp")
}

impl Instruction {
    fn to_code(&self, context: &mut Context, is_toplevel: bool) -> Result<String> {
        match self {
            Self::Assignment { name, value } => {
                let into_rax =
                    context.eval_into(value.clone(), Location::Register(Register::Rax))?;
                let into_variable = context.assign_var(name.clone(), Register::Rax, is_toplevel);
                Ok(format!("{into_rax} \n{into_variable}"))
            }
            Self::Send { to, value } => context.eval_into(
                Value::Call {
                    function: String::from("send_actor"),
                    args: vec![to.clone(), value.clone()],
                },
                Location::Register(Register::Rax),
            ),
            Self::Return(v) => {
                let into_rax = context.eval_into(v.clone(), Location::Register(Register::Rax))?;
                Ok(format!("{into_rax}\nleave\nret"))
            }
            Self::If {
                cond,
                then,
                otherwise,
            } => context.gen_if(cond.clone(), then.clone(), otherwise.clone()),
            Self::Actor(a) => context.gen_actor(a.clone(), is_toplevel, false),
            Self::Daemon(a) => context.gen_actor(a.clone(), is_toplevel, true),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    Variable(String),
    Literal(Literal),
    Call { function: String, args: Vec<Value> },
}

#[derive(Clone, Debug)]
pub enum Literal {
    String(String),
    Number(f32),
    Bool(bool),
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Number(f) => format!(".float {f}"),
            Self::Bool(b) => {
                let b = if *b { 1 } else { 0 };
                format!(".quad {b}")
            }
            Self::String(s) => {
                format!(".asciz \"{s}\"")
            }
        };
        write!(f, "{s}")
    }
}

#[derive(Clone)]
pub struct Context {
    literals: HashMap<usize, Literal>,
    symbols: HashMap<String, Address>,
    literal_counter: usize,
    stack_offset: usize,
    label_count: usize,
    actors: Vec<(String, String, String)>,
    daemons: Vec<(String, String, String)>,
    max_size: usize,
}

#[derive(PartialEq, Eq, Clone)]
enum Address {
    Local(usize),
    Global(String),
}

fn get_align(literal: &Literal) -> usize {
    match literal {
        Literal::String(_) => 1,
        Literal::Number(_) => 4,
        Literal::Bool(_) => 8,
    }
}

impl Context {
    pub fn new() -> Self {
        let literals = HashMap::new();
        let symbols = HashMap::new();
        Self {
            literals,
            symbols,
            literal_counter: 0,
            stack_offset: 0,
            label_count: 0,
            actors: vec![],
            daemons: vec![],
            max_size: 0,
        }
    }

    fn merge(&mut self, other: &Context) {
        merge(&mut self.literals, &other.literals);
        self.literal_counter = other.literal_counter;
        self.label_count = other.label_count;
    }

    fn setlabel(&mut self, label: &str) -> String {
        let label_id = self.label_count;
        self.label_count += 1;
        format!("{label}_{label_id}")
    }

    fn gen_block(&mut self, block: Vec<Instruction>) -> Result<String> {
        let mut instrs = String::new();
        for instr in block {
            instrs.push_str(&instr.to_code(self, false)?);
            instrs.push('\n');
        }
        Ok(instrs)
    }

    fn gen_actor(&mut self, actor: Actor, is_toplevel: bool, is_daemon: bool) -> Result<String> {
        let ending = self.assign_var(actor.name.clone(), Register::Rax, is_toplevel);

        let mut init_ctx = self.clone();
        let load_rt = init_ctx.assign_var(String::from("RUNTIME"), Register::Rdi, false);
        init_ctx.stack_offset = 0;
        let init_block = init_ctx.gen_block(actor.init.body.clone())?;

        let init_epilogue = vec![
            format!("push %rbp"),
            format!("mov %rsp, %rbp"),
            format!("sub ${}, %rsp", init_ctx.max_size),
            load_rt,
            init_block,
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        self.merge(&init_ctx);

        let mut update_ctx = self.clone();
        update_ctx.stack_offset = 0;
        let mut into_var = update_ctx.assign_var(actor.update.arg.clone(), Register::Rsi, false);
        let load_state = update_ctx.assign_var(actor.state_name.clone(), Register::Rdx, false);
        let load_rt = update_ctx.assign_var(String::from("RUNTIME"), Register::Rdi, false);
        into_var.push_str(&format!("\n{load_state}"));
        let update_block = update_ctx.gen_block(actor.update.body.clone())?;
        into_var.push_str(&format!("\n{update_block}"));

        let update_epilogue = vec![
            format!("push %rbp"),
            format!("mov %rsp, %rbp"),
            format!("sub ${}, %rsp", update_ctx.max_size),
            load_rt,
            into_var,
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        self.merge(&update_ctx);
        let rest = self.setlabel("rest");
        let init = self.setlabel("init");
        let update = self.setlabel("update");

        let res = vec![
            format!("jmp {rest}"),
            format!("{init}:"),
            init_epilogue,
            align_call(),
            format!("call make_undefined"),
            format!("leave"),
            format!("ret"),
            format!("{update}:"),
            update_epilogue,
            align_call(),
            format!("call make_undefined"),
            format!("leave"),
            format!("ret"),
            format!("{rest}:"),
            if !is_toplevel {
                vec![
                    format!("lea {init}(%rip), %rdi"),
                    format!("lea {update}(%rip), %rsi"),
                    align_call(),
                    if is_daemon {
                        format!("call make_daemon")
                    } else {
                        format!("call make_actor")
                    },
                    self.mv(
                        Location::Register(Register::Rax),
                        Location::Variable(self.symbols[&actor.name].clone()),
                    ),
                ]
                .join("\n")
            } else {
                String::new()
            },
            ending,
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        if is_daemon {
            self.daemons
                .push((actor.name.clone(), init.clone(), update.clone()));
        } else {
            self.actors
                .push((actor.name.clone(), init.clone(), update.clone()));
        }

        Ok(res)
    }

    fn gen_if(
        &mut self,
        cond: Value,
        then: Vec<Instruction>,
        otherwise: Vec<Instruction>,
    ) -> Result<String> {
        let eval_cond = self.eval_into(
            Value::Call {
                function: String::from("eval_conditional"),
                args: vec![cond],
            },
            Location::Register(Register::Rax),
        )?;

        let mut then_ctx = self.clone();
        let mut then_block = String::new();
        for instr in then {
            then_block.push_str(&instr.to_code(&mut then_ctx, false)?);
            then_block.push('\n')
        }
        self.merge(&then_ctx);
        self.max_size = usize::max(self.max_size, then_ctx.max_size);

        let mut otherwise_ctx = self.clone();

        let mut otherwise_block = String::new();
        for instr in otherwise {
            otherwise_block.push_str(&instr.to_code(&mut otherwise_ctx, false)?);
            otherwise_block.push('\n');
        }
        self.merge(&otherwise_ctx);
        self.max_size = usize::max(self.max_size, otherwise_ctx.max_size);
        let then = self.setlabel("then");
        let otherwise = self.setlabel("otherwise");
        let rest = self.setlabel("rest");

        let res = vec![
            eval_cond,
            format!("test %rax, %rax"),
            format!("jz {otherwise}"),
            format!("{then}:"),
            format!("{then_block}"),
            format!("jmp {rest}"),
            format!("{otherwise}:"),
            format!("{otherwise_block}"),
            format!("{rest}:"),
        ]
        .into_iter()
        .fold(String::new(), |acc, s| format!("{acc}\n{s}"));

        Ok(res)
    }

    fn get_var(&self, name: &str) -> Address {
        self.symbols.get(name).unwrap().clone()
    }

    pub fn to_code(&mut self, instructions: Vec<Instruction>) -> Result<String> {
        let actors: Vec<_> = instructions
            .iter()
            .filter_map(|instr| match instr {
                Instruction::Actor(a) => Some(a),
                _ => None,
            })
            .cloned()
            .collect();

        for actor in actors {
            self.assign_var(actor.name, Register::Rax, true);
        }

        let mut code = String::new();

        for instr in instructions {
            code.push_str(&instr.to_code(self, true)?);
        }

        let literals = self
            .literals
            .iter()
            .map(|(name, val)| format!(".align {}\nlit_{name}: {val}", get_align(val)))
            .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        //let epilogue = vec![
        //    format!("push %rbp"),
        //    format!("mov %rsp, %rbp"),
        //    format!("sub ${}, %rsp", self.max_size),
        //]
        //.into_iter()
        //.fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        let make_actors = self
            .actors
            .clone()
            .into_iter()
            .map(|(name, init, update)| {
                vec![
                    format!("lea {init}(%rip), %rdi"),
                    format!("lea {update}(%rip), %rsi"),
                    align_call(),
                    format!("call make_actor_global"),
                    self.mv(
                        Location::Register(Register::Rax),
                        Location::Variable(self.get_var(&name)),
                    ),
                    self.mv(
                        Location::Variable(self.get_var(&name)),
                        Location::Register(Register::Rdi),
                    ),
                    align_call(),
                    format!("call make_static"),
                ]
                .join("\n")
            })
            .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        let res = vec![
            format!(".data"),
            format!("{literals}"),
            format!(".text"),
            format!(".globl _start"),
            format!("_start:"),
            //epilogue,
            format!("{code}"),
            make_actors,
            align_call(),
            format!("call start_runtime"),
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"))
        .lines()
        .filter(|line| !line.trim().is_empty())
        .fold(String::new(), |acc, line| format!("{acc}\n{line}"));

        Ok(res)
    }

    fn make_literal(&mut self, literal: Literal) -> (String, Location) {
        let l_id = self.literal_counter;
        self.literal_counter += 1;
        self.literals.insert(l_id, literal.clone());
        let lit = Location::Symbol(format!("lit_{l_id}"));

        let funct = match literal {
            Literal::Bool(_) => "make_gc_bool",
            Literal::Number(_) => "make_gc_number",
            Literal::String(_) => "make_gc_string",
        };

        let target = if let Literal::Number(_) = literal {
            Register::Xmm0
        } else {
            Register::Rsi
        };

        let load_rt = self.load_rt();

        let mv = self.mv(lit, Location::Register(target.clone()));
        let code = if funct == "make_gc_string" {
            format!(
                "{load_rt}\nlea lit_{l_id}(%rip), %{target} \n{}\ncall {funct}",
                align_call()
            )
        } else {
            format!("{load_rt}\n{mv} \n{}\ncall {funct}", align_call())
        };

        (code, Location::Register(Register::Rax))
    }

    fn load_rt(&mut self) -> String {
        self.eval_into(
            Value::Variable(format!("RUNTIME")),
            Location::Register(Register::Rdi),
        )
        .unwrap_or(
            vec![
                align_call(),
                format!("call get_runtime"),
                self.mv(
                    Location::Register(Register::Rax),
                    Location::Register(Register::Rdi),
                ),
            ]
            .join("\n"),
        )
    }

    fn eval_into(&mut self, value: Value, dest: Location) -> Result<String> {
        match value {
            Value::Literal(l) => {
                let (source_code, source) = self.make_literal(l);
                let move_code = self.mv(source, dest);
                Ok(format!("{source_code} \n{move_code}"))
            }
            Value::Variable(s) => {
                let source = self.get_variable(s)?;
                let move_code = self.mv(source, dest);
                Ok(move_code)
            }
            Value::Call {
                function,
                args: mut rest,
            } => {
                let mut args = vec![Value::Variable(format!("RUNTIME"))];
                args.append(&mut rest);
                let mut ids = vec![];
                let spilled: Result<Vec<String>> = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| {
                        let id = self.allocate_space(format!("${i}"));
                        ids.push(id);
                        self.eval_into(arg.clone(), Location::Variable(Address::Local(id)))
                    })
                    .collect();

                let arg_registers =
                    vec![Register::Rdi, Register::Rsi, Register::Rdx, Register::Rcx];

                let mut spilled = spilled?;

                let into_registers = args
                    .into_iter()
                    .enumerate()
                    .map(|(i, _)| format!("mov -{}(%rbp), %{}", ids[i], arg_registers[i]))
                    .chain(iter::once(format!(
                        "{}\n{}\n{}\ncall {function}\n{}",
                        align_call(),
                        self.load_rt(),
                        align_call(),
                        self.mv(Location::Register(Register::Rax), dest)
                    )))
                    .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

                spilled.push(into_registers);

                Ok(spilled.join("\n"))
            }
        }
    }

    fn get_variable(&mut self, name: String) -> Result<Location> {
        Ok(Location::Variable(
            self.symbols
                .get(&name)
                .ok_or(format!("Unknown variable {name}"))?
                .clone(),
        ))
    }

    fn mv(&mut self, source: Location, dest: Location) -> String {
        if source == dest {
            return String::new();
        }
        let op = if dest.is_simd_register() || source.is_simd_register() {
            String::from("movss")
        } else {
            String::from("mov")
        };

        if source.is_memory() && dest.is_memory() {
            vec![
                self.mv(source, Location::Register(Register::Rax)),
                self.mv(Location::Register(Register::Rax), dest),
            ]
            .join("\n")
        } else {
            let source = source.as_gas_text();

            let dest = dest.as_gas_text();

            format!("{op} {source}, {dest}")
        }
    }

    fn allocate_space(&mut self, name: String) -> usize {
        self.stack_offset += 8;
        self.max_size = usize::max(self.stack_offset, self.max_size);
        self.symbols.insert(name, Address::Local(self.stack_offset));
        self.stack_offset
    }

    fn assign_var(&mut self, name: String, register: Register, global: bool) -> String {
        if global {
            self.symbols.entry(name).or_insert_with(|| {
                let l_id = self.literal_counter;
                self.literal_counter += 1;
                self.literals.insert(l_id, Literal::Bool(false));
                Address::Global(format!("lit_{l_id}"))
            });
            return String::new();
        }
        let offset = self.allocate_space(name);
        self.mv(
            Location::Register(register),
            Location::Variable(Address::Local(offset)),
        )
    }
}

#[derive(PartialEq, Eq)]
enum Location {
    Register(Register),
    Symbol(String),
    Variable(Address),
}

impl Location {
    fn is_simd_register(&self) -> bool {
        match self {
            Self::Register(r) => r.is_simd(),
            _ => false,
        }
    }

    fn as_gas_text(&self) -> String {
        match self {
            Self::Register(r) => format!("%{r}"),
            Self::Symbol(s) => format!("{s}(%rip)"),
            Self::Variable(Address::Local(v)) => format!("-{v}(%rbp)"),
            Self::Variable(Address::Global(a)) => format!("{a}(%rip)"),
        }
    }

    fn is_memory(&self) -> bool {
        match self {
            Self::Register(_) => false,
            _ => true,
        }
    }
}

#[allow(unused)]
#[derive(PartialEq, Eq, Clone)]
enum Register {
    // General-purpose registers
    Rax,
    Rbx,
    Rcx,
    Rdx,
    Rsi,
    Rdi,
    Rbp,
    Rsp,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,

    // SIMD registers
    Xmm0,
    Xmm1,
    Xmm2,
    Xmm3,
    Xmm4,
    Xmm5,
    Xmm6,
    Xmm7,
    Xmm8,
    Xmm9,
    Xmm10,
    Xmm11,
    Xmm12,
    Xmm13,
    Xmm14,
    Xmm15,
}

impl Register {
    fn is_simd(&self) -> bool {
        matches!(
            self,
            Register::Xmm0
                | Register::Xmm1
                | Register::Xmm2
                | Register::Xmm3
                | Register::Xmm4
                | Register::Xmm5
                | Register::Xmm6
                | Register::Xmm7
                | Register::Xmm8
                | Register::Xmm9
                | Register::Xmm10
                | Register::Xmm11
                | Register::Xmm12
                | Register::Xmm13
                | Register::Xmm14
                | Register::Xmm15
        )
    }
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let reg_name = match self {
            Register::Rax => "rax",
            Register::Rbx => "rbx",
            Register::Rcx => "rcx",
            Register::Rdx => "rdx",
            Register::Rsi => "rsi",
            Register::Rdi => "rdi",
            Register::Rbp => "rbp",
            Register::Rsp => "rsp",
            Register::R8 => "r8",
            Register::R9 => "r9",
            Register::R10 => "r10",
            Register::R11 => "r11",
            Register::R12 => "r12",
            Register::R13 => "r13",
            Register::R14 => "r14",
            Register::R15 => "r15",
            Register::Xmm0 => "xmm0",
            Register::Xmm1 => "xmm1",
            Register::Xmm2 => "xmm2",
            Register::Xmm3 => "xmm3",
            Register::Xmm4 => "xmm4",
            Register::Xmm5 => "xmm5",
            Register::Xmm6 => "xmm6",
            Register::Xmm7 => "xmm7",
            Register::Xmm8 => "xmm8",
            Register::Xmm9 => "xmm9",
            Register::Xmm10 => "xmm10",
            Register::Xmm11 => "xmm11",
            Register::Xmm12 => "xmm12",
            Register::Xmm13 => "xmm13",
            Register::Xmm14 => "xmm14",
            Register::Xmm15 => "xmm15",
        };
        write!(f, "{}", reg_name)
    }
}

pub fn gen_instructions(cst: Cst) -> Vec<Instruction> {
    cst.into_iter()
        .map(|a| match a {
            ActorKind::Daemon(a) => Statement::Daemon(a),
            ActorKind::Actor(a) => Statement::Actor(a),
        })
        .map(|s| s.to_instr())
        .collect()
}
