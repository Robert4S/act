use core::fmt;
use std::collections::HashMap;

fn merge<K: Clone, V: Clone>(map1: &mut HashMap<K, V>, map2: &HashMap<K, V>) -> ()
where
    K: Eq + std::hash::Hash,
{
    for (k, v) in map2 {
        map1.entry(k.clone()).or_insert(v.clone()); // inserts only if key is not already present
    }
}

#[derive(Clone)]
struct Update {
    arg: String,
    body: Vec<Instruction>,
}

#[derive(Clone)]
struct Init {
    body: Vec<Instruction>,
}

#[derive(Clone)]
struct Actor {
    name: String,
    update: Update,
    init: Init,
}

#[derive(Clone)]
enum Instruction {
    Assignment {
        name: String,
        value: Value,
    },
    Send {
        to: Value,
        value: Value,
    },
    Actor(Actor),
    Return(Value),
    SetLabel(String),
    If {
        cond: Value,
        then: Vec<Instruction>,
        otherwise: Vec<Instruction>,
    },
}

impl Instruction {
    fn to_code(&self, context: &mut Context) -> Option<String> {
        match self {
            Self::Assignment { name, value } => {
                let into_rax =
                    context.eval_into(value.clone(), Location::Register(Register::Rax))?;
                let into_variable = context.assign_var(name.clone(), Register::Rax);
                Some(format!("{into_rax} \n{into_variable}"))
            }
            Self::Send { to, value } => {
                let into_rdi = context.eval_into(to.clone(), Location::Register(Register::Rdi))?;
                let into_temp = context.assign_var(format!("to"), Register::Rdi);
                let into_rsi =
                    context.eval_into(value.clone(), Location::Register(Register::Rsi))?;
                let back_in = context.mv(
                    Location::Variable(context.symbols["to"]),
                    Location::Register(Register::Rdi),
                );
                let res = vec![
                    into_rdi,
                    into_temp,
                    into_rsi,
                    back_in,
                    format!("call send_actor"),
                ]
                .into_iter()
                .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));
                Some(res)
            }
            Self::Return(v) => {
                let into_rax = context.eval_into(v.clone(), Location::Register(Register::Rax))?;
                Some(format!("{into_rax}\nleave\nret"))
            }
            Self::SetLabel(s) => Some(format!("{s}:")),
            Self::If {
                cond,
                then,
                otherwise,
            } => context.gen_if(cond.clone(), then.clone(), otherwise.clone()),
            Self::Actor(a) => context.gen_actor(a.clone()),
        }
    }
}

#[derive(Clone, Debug)]
enum Value {
    Variable(String),
    Literal(Literal),
}

#[derive(Clone, Debug)]
enum Literal {
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
    symbols: HashMap<String, usize>,
    literal_counter: usize,
    stack_offset: usize,
    label_count: usize,
    actors: Vec<Actor>,
    max_size: usize,
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
            max_size: 0,
        }
    }

    fn merge(&mut self, other: &Context) {
        merge(&mut self.literals, &other.literals);
        self.literal_counter = other.literal_counter;
        self.label_count = other.label_count;
    }

    pub fn test(&mut self) -> () {
        let assignment = Instruction::Assignment {
            name: String::from("hello_world"),
            value: Value::Literal(Literal::Number(3.141)),
        };

        let other_assignment = Instruction::Assignment {
            name: String::from("goodbye_world"),
            value: Value::Literal(Literal::Number(6.28)),
        };

        let ret = Instruction::Return(Value::Variable(String::from("goodbye_world")));

        let if_instr = Instruction::If {
            cond: Value::Literal(Literal::Bool(true)),
            then: vec![assignment],
            otherwise: vec![other_assignment, ret],
        };

        let s2 = Instruction::If {
            cond: Value::Literal(Literal::Bool(false)),
            then: vec![Instruction::Return(Value::Literal(Literal::Number(2.5)))],
            otherwise: vec![Instruction::Return(Value::Literal(Literal::String(
                format!("hello_world!"),
            )))],
        };

        let update = Update {
            arg: format!("arg"),
            body: vec![if_instr, s2],
        };

        let init = Init {
            body: vec![Instruction::Return(Value::Literal(Literal::Number(2.73)))],
        };

        let actor = Actor {
            name: format!("Yur"),
            update,
            init,
        };

        let out = self.to_code(vec![Instruction::Actor(actor)]).unwrap();
        println!("{out}");
    }

    fn setlabel(&mut self, label: &str) -> String {
        let label_id = self.label_count;
        self.label_count += 1;
        format!("{label}_{label_id}")
    }

    fn gen_block(&mut self, block: Vec<Instruction>) -> Option<String> {
        let mut instrs = String::new();
        for instr in block {
            instrs.push_str(&instr.to_code(self)?);
            instrs.push('\n');
        }
        Some(instrs)
    }

    fn gen_actor(&mut self, actor: Actor) -> Option<String> {
        let mut init_ctx = self.clone();
        init_ctx.stack_offset = 0;
        let init_block = init_ctx.gen_block(actor.init.body.clone())?;

        let init_epilogue = vec![
            format!("push %rbp"),
            format!("mov %rsp, %rbp"),
            format!("sub ${}, %rsp", init_ctx.max_size),
            init_block,
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        self.merge(&init_ctx);

        let mut update_ctx = self.clone();
        update_ctx.stack_offset = 0;
        let mut into_var = update_ctx.assign_var(actor.update.arg.clone(), Register::Rdi);
        let load_state = update_ctx.assign_var(format!("state"), Register::Rsi);
        into_var.push_str(&format!("\n{load_state}"));
        let update_block = update_ctx.gen_block(actor.update.body.clone())?;
        into_var.push_str(&update_block);

        let update_epilogue = vec![
            format!("push %rbp"),
            format!("mov %rsp, %rbp"),
            format!("sub ${}, %rsp", update_ctx.max_size),
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
            format!("call make_undefined"),
            format!("leave"),
            format!("ret"),
            format!("{update}:"),
            update_epilogue,
            format!("call make_undefined"),
            format!("leave"),
            format!("ret"),
            format!("{rest}:"),
            format!("lea {init}(%rip), %rdi"),
            format!("lea {update}(%rip), %rsi"),
            format!("call make_actor"),
            self.assign_var(actor.name.clone(), Register::Rax),
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        self.actors.push(actor);

        Some(res)
    }

    fn gen_if(
        &mut self,
        cond: Value,
        then: Vec<Instruction>,
        otherwise: Vec<Instruction>,
    ) -> Option<String> {
        let into_rdi = self.eval_into(cond, Location::Register(Register::Rdi))?;

        let mut then_ctx = self.clone();
        let mut then_block = String::new();
        for instr in then {
            then_block.push_str(&instr.to_code(&mut then_ctx)?);
            then_block.push('\n')
        }
        self.merge(&then_ctx);
        self.max_size = usize::max(self.max_size, then_ctx.max_size);

        let mut otherwise_ctx = self.clone();

        let mut otherwise_block = String::new();
        for instr in otherwise {
            otherwise_block.push_str(&instr.to_code(&mut otherwise_ctx)?);
            otherwise_block.push('\n');
        }
        self.merge(&otherwise_ctx);
        self.max_size = usize::max(self.max_size, otherwise_ctx.max_size);
        let then = self.setlabel("then");
        let otherwise = self.setlabel("otherwise");
        let rest = self.setlabel("rest");

        let res = vec![
            format!("{into_rdi}"),
            format!("call eval_conditional"),
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

        Some(res)
    }

    fn to_code(&mut self, instructions: Vec<Instruction>) -> Option<String> {
        let mut code = String::new();
        for instr in instructions {
            code.push_str(&instr.to_code(self)?);
        }
        let literals = self
            .literals
            .iter()
            .map(|(name, val)| format!("lit_{name}: {val}"))
            .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        let epilogue = vec![
            format!("push %rbp"),
            format!("mov %rsp, %rbp"),
            format!("sub ${}, %rsp", self.max_size),
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"));

        let res = vec![
            format!(".data"),
            format!("{literals}"),
            format!(".text"),
            format!(".globl _start"),
            format!("_start:"),
            epilogue,
            format!("{code}"),
            format!("call start_runtime"),
        ]
        .into_iter()
        .fold(String::new(), |acc, instr| format!("{acc}\n{instr}"))
        .lines()
        .filter(|line| !line.trim().is_empty())
        .fold(String::new(), |acc, line| format!("{acc}\n{line}"));

        Some(res)
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
            Register::Rdi
        };

        let mv = self.mv(lit, Location::Register(target));
        let code = format!("{mv} \ncall {funct}");
        (code, Location::Register(Register::Rax))
    }

    fn eval_into(&mut self, value: Value, dest: Location) -> Option<String> {
        match value {
            Value::Literal(l) => {
                let (source_code, source) = self.make_literal(l);
                let move_code = self.mv(source, dest);
                Some(format!("{source_code} \n{move_code}"))
            }
            Value::Variable(s) => {
                let source = self.get_variable(s)?;
                let move_code = self.mv(source, dest);
                Some(move_code)
            }
        }
    }

    fn get_variable(&mut self, name: String) -> Option<Location> {
        Some(Location::Variable(*self.symbols.get(&name)?))
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

        let source = source.as_gas_text();

        let dest = dest.as_gas_text();

        format!("{op} {source}, {dest}")
    }

    fn allocate_space(&mut self) -> usize {
        self.stack_offset += 8;
        self.max_size = usize::max(self.stack_offset, self.max_size);
        self.stack_offset
    }

    fn assign_var(&mut self, name: String, register: Register) -> String {
        let offset = self.allocate_space();
        self.symbols.insert(name, offset);
        self.mv(Location::Register(register), Location::Variable(offset))
    }
}

#[derive(PartialEq, Eq)]
enum Location {
    Register(Register),
    Symbol(String),
    Variable(usize),
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
            Self::Variable(v) => format!("-{v}(%rbp)"),
        }
    }
}

#[derive(PartialEq, Eq)]
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
