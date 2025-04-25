use std::{
    collections::{BTreeSet, HashMap},
    convert::identity,
    fs::File,
    io::Write,
    iter,
};

use codegen::{ir::immediates::Offset32, write_function};
use cranelift::{
    frontend::FuncInstBuilder,
    module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError},
    object::{ObjectBuilder, ObjectModule},
    prelude::*,
};
use isa::CallConv;

use super::frontend::{
    cst::{self, Cst, Expr, Forall, ForallElim, Statement},
    tokenise::InfixToken,
};

fn declare_variables(
    int: types::Type,
    builder: &mut FunctionBuilder,
    params: &[String],
    body: &[Statement],
    entry_block: Block,
) -> HashMap<String, Variable> {
    let mut vars = HashMap::new();
    let mut idx = 0;

    for (i, name) in params.iter().enumerate() {
        let val = builder.block_params(entry_block)[i];
        let var = declare_variable(int, builder, &mut vars, &mut idx, name);
        builder.def_var(var, val);
    }

    for stmt in body {
        declare_vars_in_stmt(int, builder, &mut vars, &mut idx, stmt);
    }

    vars
}

fn declare_vars_in_stmt(
    int: Type,
    builder: &mut FunctionBuilder,
    vars: &mut HashMap<String, Variable>,
    idx: &mut usize,
    stmt: &Statement,
) {
    match stmt {
        Statement::Assignment(assignment) => {
            declare_variable(int, builder, vars, idx, &assignment.left);
        }
        Statement::If {
            condition: _,
            body,
            otherwise,
        } => {
            for stmt in body {
                declare_vars_in_stmt(int, builder, vars, idx, stmt);
            }

            if let Some(body) = otherwise {
                for stmt in body {
                    declare_vars_in_stmt(int, builder, vars, idx, stmt);
                }
            }
        }
        _ => (),
    }
}

fn declare_variable(
    int: types::Type,
    builder: &mut FunctionBuilder,
    variables: &mut HashMap<String, Variable>,
    index: &mut usize,
    name: &str,
) -> Variable {
    let var = Variable::new(*index);
    if !variables.contains_key(name) {
        variables.insert(name.into(), var);
        builder.declare_var(var, int);
        *index += 1;
    }
    var
}

#[derive(Clone, Debug)]
struct Actor {
    pid_slot: DataId,
    init: FuncId,
    update: FuncId,
}

pub struct Compiler {
    builder_ctx: FunctionBuilderContext,
    ctx: codegen::Context,
    data_description: DataDescription,
    module: ObjectModule,
    actors: Vec<Actor>,
    literal_counter: usize,
    globals: BTreeSet<String>,
    statics: HashMap<Constant, DataId>,
    pub debug: bool,
}

impl Default for Compiler {
    fn default() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "true").unwrap();

        let isa_builder = cranelift::native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });

        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();

        let builder =
            ObjectBuilder::new(isa, "main", cranelift::module::default_libcall_names()).unwrap();

        let module = ObjectModule::new(builder);

        let mut ctx = module.make_context();
        ctx.func.signature.call_conv = CallConv::SystemV;

        Self {
            builder_ctx: FunctionBuilderContext::new(),
            ctx,
            data_description: DataDescription::new(),
            module,
            actors: Vec::default(),
            literal_counter: 0,
            globals: BTreeSet::default(),
            debug: false,
            statics: HashMap::new(),
        }
    }
}

#[derive(PartialEq, PartialOrd, Hash, Clone, Eq, Ord)]
enum Constant {
    Number(i64),
    Bool(u8),
}

impl Compiler {
    pub fn finish(self, file: &str) {
        let mut file = File::create(file).unwrap();
        let product = self.module.finish().emit().unwrap();
        file.write(&product).unwrap();
    }

    pub fn compile(&mut self, cst: Cst) -> Result<(), ModuleError> {
        self.data_description.clear();
        let mut slots = vec![];
        for a in &cst.actors {
            let name = &a.name;
            self.globals.insert(name.clone());
            let pid_slot = self
                .module
                .declare_data(name, Linkage::Export, true, false)
                .unwrap();
            self.data_description.define_zeroinit(8);
            self.data_description.set_align(8);
            self.module
                .define_data(pid_slot, &self.data_description)
                .unwrap();
            self.data_description.clear();

            slots.push(pid_slot);
        }

        for (idx, a) in cst.actors.into_iter().enumerate() {
            let pid_slot = slots[idx];

            self.translate_actor(a, pid_slot).unwrap();
        }

        self.ctx.clear();
        self.ctx.func.signature.call_conv = CallConv::SystemV;

        self.start_prog().unwrap();

        Ok(())
    }

    fn translate_actor(&mut self, actor: cst::Actor, pid_slot: DataId) -> Result<(), ModuleError> {
        let a = actor;
        if self.debug {
            println!("Actor {}", a.name);
        }

        self.ctx.clear();
        self.ctx.func.signature.call_conv = CallConv::SystemV;

        // Translate init function
        self.translate(
            vec![String::from("RUNTIME")],
            a.initialiser.body.clone().into_iter().collect(),
        )
        .unwrap();

        let init_id = self
            .module
            .declare_function(
                &format!("{}_init", a.name),
                Linkage::Export,
                &self.ctx.func.signature,
            )
            .unwrap();

        self.module.define_function(init_id, &mut self.ctx).unwrap();

        self.ctx.clear();
        self.ctx.func.signature.call_conv = CallConv::SystemV;

        if self.debug {
            println!("UPDATE:");
        }
        self.translate(
            vec![
                String::from("RUNTIME"),
                a.update.inp_name.clone(),
                a.state.name.clone(),
            ],
            a.update.body.into_iter().collect(),
        )
        .unwrap();

        let update_id = self
            .module
            .declare_function(
                &format!("{}_update", a.name),
                Linkage::Export,
                &self.ctx.func.signature,
            )
            .unwrap();

        self.module
            .define_function(update_id, &mut self.ctx)
            .unwrap();

        self.ctx.clear();
        self.ctx.func.signature.call_conv = CallConv::SystemV;

        let actor_id = Actor {
            pid_slot,
            init: init_id,
            update: update_id,
        };

        self.actors.push(actor_id);

        Ok(())
    }

    fn start_prog(&mut self) -> Result<(), ModuleError> {
        if self.debug {
            println!("MAIN:");
        }
        let int = self.module.target_config().pointer_type();
        self.ctx.func.signature.call_conv = CallConv::SystemV;
        self.ctx.func.signature.returns.push(AbiParam::new(int));

        let start = self
            .module
            .declare_function("main", Linkage::Export, &self.ctx.func.signature)
            .unwrap();

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        //
        // TODO: Streamline the API here.
        builder.append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_block);
        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        // The toy language allows variables to be declared implicitly.
        // Walk the AST and declare all implicitly-declared variables.

        // Now translate the statements of the function body.
        //
        let ret_block = builder.create_block();

        let actors = self.actors.clone();

        let mut trans = FunctionTranslator {
            constants: &mut self.statics,
            int,
            builder,
            vars: HashMap::new(),
            module: &mut self.module,
            data_description: &mut self.data_description,
            globals: &self.globals,
            literal_count: &mut self.literal_counter,
            ret_block,
        };

        for actor in actors {
            trans.define_actor(actor);
        }

        trans.translate_call("start_runtime".to_string(), vec![]);
        trans.builder.ins().jump(ret_block, &[]);
        trans.builder.seal_block(ret_block);
        trans.builder.switch_to_block(ret_block);
        let zero = trans.builder.ins().iconst(int, 0);
        trans.builder.ins().return_(&[zero]);

        if self.debug {
            let mut s = String::new();
            write_function(&mut s, &trans.builder.func).unwrap();
            println!("{s}");
        }
        // Tell the builder we're done with this function.
        trans.builder.finalize();

        self.module.define_function(start, &mut self.ctx).unwrap();

        self.ctx.clear();
        self.ctx.func.signature.call_conv = CallConv::SystemV;

        Ok(())
    }

    fn translate(&mut self, params: Vec<String>, stmts: Vec<Statement>) -> Result<(), ModuleError> {
        let int = self.module.target_config().pointer_type();

        for _p in &params {
            self.ctx.func.signature.params.push(AbiParam::new(int));
        }

        self.ctx.func.signature.returns.push(AbiParam::new(int));

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_ctx);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        //
        // TODO: Streamline the API here.
        builder.append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        // The toy language allows variables to be declared implicitly.
        // Walk the AST and declare all implicitly-declared variables.
        let vars = declare_variables(int, &mut builder, &params, &stmts, entry_block);

        let ret_block = builder.create_block();

        // Now translate the statements of the function body.
        let mut trans = FunctionTranslator {
            int,
            builder,
            vars,
            module: &mut self.module,
            data_description: &mut self.data_description,
            globals: &self.globals,
            literal_count: &mut self.literal_counter,
            ret_block,
            constants: &mut self.statics,
        };

        let returns = stmts
            .into_iter()
            .map(|s| trans.translate_stmt(s))
            .any(identity);

        // We can guarantee that if a function has ANY path that doesnt return, the actor's state
        // type must be Unit
        if !returns {
            let rt = trans.get_runtime();
            let unit = trans.translate_call("make_gc_unit".to_string(), vec![rt]);
            trans.builder.ins().jump(trans.ret_block, &[unit]);
        }

        trans
            .builder
            .append_block_params_for_function_returns(ret_block);

        trans.builder.switch_to_block(ret_block);
        let ret_param = trans.builder.block_params(ret_block)[0];

        trans.builder.ins().return_(&[ret_param]);

        trans.builder.seal_block(ret_block);

        if self.debug {
            let mut s = String::new();
            write_function(&mut s, &trans.builder.func).unwrap();
            println!("{s}");
        }

        trans.builder.finalize();
        Ok(())
    }
}

struct FunctionTranslator<'a> {
    int: types::Type,
    vars: HashMap<String, Variable>,
    builder: FunctionBuilder<'a>,
    module: &'a mut ObjectModule,
    data_description: &'a mut DataDescription,
    globals: &'a BTreeSet<String>,
    literal_count: &'a mut usize,
    ret_block: Block,
    constants: &'a mut HashMap<Constant, DataId>,
}

impl<'a> FunctionTranslator<'a> {
    fn define_actor(&mut self, actor: Actor) {
        let init_ref = self
            .module
            .declare_func_in_func(actor.init, &mut self.builder.func);

        let update_ref = self
            .module
            .declare_func_in_func(actor.update, &mut self.builder.func);

        let init_ptr = self.builder.ins().func_addr(self.int, init_ref);
        let update_ptr = self.builder.ins().func_addr(self.int, update_ref);

        let pid_slot_ref = self
            .module
            .declare_data_in_func(actor.pid_slot, &mut self.builder.func);

        let pid_slot_addr = self.builder.ins().symbol_value(self.int, pid_slot_ref);

        let name = "make_actor_global".to_string();

        self.translate_call(
            name,
            vec![
                (init_ptr, self.int),
                (update_ptr, self.int),
                (pid_slot_addr, self.int),
            ],
        );
    }

    fn translate_stmt(&mut self, stmt: Statement) -> bool {
        match stmt {
            Statement::Assignment(assignment) => {
                let name = assignment.left;
                let val = self.translate_expr(assignment.right);
                let variable = self
                    .vars
                    .get(&name)
                    .expect(&format!("undeclared variable {name}"));

                self.builder.def_var(*variable, val);

                false
            }
            Statement::Return(expr) => {
                let ret_val = self.translate_expr(expr);
                self.builder.ins().jump(self.ret_block, &[ret_val]);
                true
            }
            Statement::Actor(_actor) => todo!(),
            Statement::Daemon(_actor) => todo!(),
            Statement::Send { destination, value } => {
                let destination = self.translate_expr(destination);
                let value = self.translate_expr(value);
                let rt = self.get_runtime();
                self.translate_call(
                    String::from("send_actor"),
                    vec![rt, (destination, self.int), (value, self.int)],
                );

                false
            }
            Statement::If {
                condition,
                body,
                otherwise,
            } => {
                let block_then = self.builder.create_block();
                let block_else = self.builder.create_block();
                let block_merge = self.builder.create_block();
                let rt = self.get_runtime();

                let condition = self.translate_expr(condition);
                let cond =
                    self.translate_call("unmask_int".into(), vec![rt, (condition, self.int)]);

                self.builder
                    .ins()
                    .brif(cond, block_then, &[], block_else, &[]);

                self.builder.switch_to_block(block_then);
                self.builder.seal_block(block_then);

                let then_terminated = body.into_iter().map(|s| self.translate_stmt(s)).any(|x| x);

                if !then_terminated {
                    self.builder.ins().jump(block_merge, &[]);
                }

                self.builder.switch_to_block(block_else);
                self.builder.seal_block(block_else);

                let else_terminated = if let Some(else_stmts) = otherwise {
                    let else_terminated = else_stmts
                        .into_iter()
                        .map(|s| self.translate_stmt(s))
                        .any(|x| x);

                    if !else_terminated {
                        self.builder.ins().jump(block_merge, &[]);
                    }
                    else_terminated
                } else {
                    self.builder.ins().jump(block_merge, &[]);
                    false
                };

                self.builder.switch_to_block(block_merge);
                self.builder.seal_block(block_merge);

                then_terminated && else_terminated
            }
            Statement::Intrinsic { func_name, args } => {
                let rt = self.get_runtime();
                let other_args = args
                    .into_iter()
                    .map(|arg| (self.translate_expr(arg), self.int));
                let args = iter::once(rt).chain(other_args).collect();

                let _ = self.translate_call(func_name, args);
                false
            }
        }
    }

    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
            Expr::Float(f) => {
                let imm = self.builder.ins().f64const(f);
                self.make_float(imm)
            }
            Expr::Int(i) => {
                let imm = self.builder.ins().iconst(self.int, i);
                self.make_int(imm)
            }
            Expr::String(s) => self.translate_string(s),
            Expr::Symbol(name) => self.translate_symbol(name),
            Expr::Bool(b) => {
                let imm = self.builder.ins().iconst(self.int, b as i64);
                self.make_bool(imm)
            }

            Expr::Infix {
                left,
                op,
                right,
                eq_typename_buf,
            } => {
                let left_v = self.translate_expr(*left.clone());
                let right_v = self.translate_expr(*right);
                if let Some(v) = self.direct_infix(left_v, op.clone(), right_v) {
                    v
                } else {
                    self.translate_eq(left_v, right_v, &eq_typename_buf.borrow())
                }
            }
            Expr::ForallElim(ForallElim { expr, args: _ }) => self.translate_expr(*expr),
            Expr::Forall(Forall { vars: _, then }) => self.translate_expr(*then),
        }
    }

    fn translate_eq(&mut self, left: Value, right: Value, _name: &String) -> Value {
        let rt = self.get_runtime();
        self.translate_call(
            "eq_val".to_string(),
            vec![rt, (left, self.int), (right, self.int)],
        )
    }

    fn direct_infix(&mut self, left: Value, op: InfixToken, right: Value) -> Option<Value> {
        let float_output: Option<Box<dyn Fn(Value, Value, FuncInstBuilder) -> Value>> = match op {
            InfixToken::PlusFloat => Some(Box::new(|left, right, ins| ins.fadd(left, right))),
            InfixToken::MinusFloat => Some(Box::new(|left, right, ins| ins.fsub(left, right))),
            InfixToken::MulFloat => Some(Box::new(|left, right, ins| ins.fmul(left, right))),
            InfixToken::DivFloat => Some(Box::new(|left, right, ins| ins.fdiv(left, right))),

            _ => None,
        };

        let int_output: Option<Box<dyn Fn(Value, Value, FuncInstBuilder) -> Value>> = match op {
            InfixToken::Plus => Some(Box::new(|left, right, ins| ins.iadd(left, right))),
            InfixToken::Minus => Some(Box::new(|left, right, ins| ins.isub(left, right))),
            InfixToken::Mul => Some(Box::new(|left, right, ins| ins.imul(left, right))),
            InfixToken::Mod => Some(Box::new(|left, right, ins| ins.srem(left, right))),

            _ => None,
        };

        let bool_output_float_input: Option<Box<dyn Fn(Value, Value, FuncInstBuilder) -> Value>> =
            match op {
                InfixToken::GreaterFloat => Some(Box::new(|left, right, ins| {
                    ins.fcmp(FloatCC::GreaterThan, left, right)
                })),
                InfixToken::LesserFloat => Some(Box::new(|left, right, ins| {
                    ins.fcmp(FloatCC::LessThan, left, right)
                })),
                InfixToken::GEFloat => Some(Box::new(|left, right, ins| {
                    ins.fcmp(FloatCC::GreaterThanOrEqual, left, right)
                })),
                InfixToken::LEFloat => Some(Box::new(|left, right, ins| {
                    ins.fcmp(FloatCC::LessThanOrEqual, left, right)
                })),
                _ => None,
            };

        let bool_output_int_input: Option<Box<dyn Fn(Value, Value, FuncInstBuilder) -> Value>> =
            match op {
                InfixToken::Greater => Some(Box::new(|left, right, ins| {
                    ins.icmp(IntCC::SignedGreaterThan, left, right)
                })),
                InfixToken::Lesser => Some(Box::new(|left, right, ins| {
                    ins.icmp(IntCC::SignedLessThan, left, right)
                })),
                InfixToken::GE => Some(Box::new(|left, right, ins| {
                    ins.icmp(IntCC::SignedGreaterThanOrEqual, left, right)
                })),
                InfixToken::LE => Some(Box::new(|left, right, ins| {
                    ins.icmp(IntCC::SignedLessThanOrEqual, left, right)
                })),
                _ => None,
            };

        let bool_output_bool_input: Option<Box<dyn Fn(Value, Value, FuncInstBuilder) -> Value>> =
            match op {
                InfixToken::And => Some(Box::new(|left, right, ins| ins.band(left, right))),
                InfixToken::Or => Some(Box::new(|left, right, ins| ins.bor(left, right))),
                _ => None,
            };

        let rt = self.get_runtime();

        if let InfixToken::Div = op {
            let rt = self.get_runtime();
            let divved = self.translate_call(
                "eval_int_div".to_string(),
                vec![rt, (left, self.int), (right, self.int)],
            );
            return Some(divved);
        }

        if let Some(f) = int_output {
            let left_int = self.translate_call("unmask_int".into(), vec![rt, (left, self.int)]);
            let right_int = self.translate_call("unmask_int".into(), vec![rt, (right, self.int)]);

            let res = f(left_int, right_int, self.builder.ins());
            Some(self.make_int(res))
        } else if let Some(f) = bool_output_int_input {
            let left_int = self.translate_call("unmask_int".into(), vec![rt, (left, self.int)]);
            let right_int = self.translate_call("unmask_int".into(), vec![rt, (right, self.int)]);
            let res = f(left_int, right_int, self.builder.ins());
            let res = self.builder.ins().sextend(self.int, res);
            Some(self.make_bool(res))
        } else if let Some(f) = float_output {
            let left_float =
                self.builder
                    .ins()
                    .load(types::F64, MemFlags::trusted(), left, Offset32::new(0));
            let right_float =
                self.builder
                    .ins()
                    .load(types::F64, MemFlags::trusted(), right, Offset32::new(0));

            let res = f(left_float, right_float, self.builder.ins());
            Some(self.make_float(res))
        } else if let Some(f) = bool_output_float_input {
            let left_float =
                self.builder
                    .ins()
                    .load(types::F64, MemFlags::trusted(), left, Offset32::new(0));
            let right_float =
                self.builder
                    .ins()
                    .load(types::F64, MemFlags::trusted(), right, Offset32::new(0));

            let res = f(left_float, right_float, self.builder.ins());
            let res = self.builder.ins().sextend(self.int, res);
            Some(self.make_bool(res))
        } else if let Some(f) = bool_output_bool_input {
            let left_int = self.translate_call("unmask_int".into(), vec![rt, (left, self.int)]);
            let right_int = self.translate_call("unmask_int".into(), vec![rt, (right, self.int)]);

            let val = f(left_int, right_int, self.builder.ins());

            Some(self.make_bool(val))
        } else {
            None
        }
    }

    fn get_runtime(&mut self) -> (Value, Type) {
        (
            self.translate_expr(Expr::Symbol("RUNTIME".to_string())),
            self.int,
        )
    }

    fn translate_symbol(&mut self, name: String) -> Value {
        if self.vars.contains_key(&name) {
            let var = self
                .vars
                .get(&name)
                .expect(&format!("Variable {name} is not defined"));
            self.builder.use_var(*var)
        } else if self.globals.contains(&name) {
            self.translate_global_data_addr(name)
        } else {
            panic!("Variable {name} is not defined")
        }
    }

    fn translate_string(&mut self, s: String) -> Value {
        let mut cstring = s.into_bytes();
        cstring.push(0);
        self.data_description.define(cstring.into_boxed_slice());
        *self.literal_count += 1;
        let name = format!("lit_{}", self.literal_count);
        let id = self
            .module
            .declare_data(&name, Linkage::Export, false, false)
            .map_err(|e| e.to_string())
            .unwrap();

        self.module.define_data(id, self.data_description).unwrap();
        self.data_description.clear();

        let local_id = self.module.declare_data_in_func(id, self.builder.func);
        let ptr = self.builder.ins().symbol_value(self.int, local_id);

        let args = vec![
            (
                self.translate_expr(Expr::Symbol(String::from("RUNTIME"))),
                self.int,
            ),
            (ptr, self.int),
        ];

        let name = String::from("make_gc_string");

        self.translate_call(name, args)
    }

    fn make_float(&mut self, number: Value) -> Value {
        let rt = self.get_runtime();
        let addr = self.translate_call("make_gc_float".to_string(), vec![rt]);
        self.builder
            .ins()
            .store(MemFlags::trusted(), number, addr, Offset32::new(0));
        addr
    }

    fn make_int(&mut self, number: Value) -> Value {
        let rt = self.get_runtime();
        let imm = self.translate_call("make_gc_int".to_string(), vec![rt, (number, self.int)]);
        imm
    }

    fn make_bool(&mut self, bool: Value) -> Value {
        let rt = self.get_runtime();
        let imm = self.translate_call("make_gc_bool".to_string(), vec![rt, (bool, self.int)]);
        imm
    }

    fn translate_call(&mut self, name: String, args: Vec<(Value, Type)>) -> Value {
        let mut sig = self.module.make_signature();
        sig.call_conv = CallConv::SystemV;

        for (_, t) in &args {
            sig.params.push(AbiParam::new(*t));
        }

        sig.returns.push(AbiParam::new(self.int));

        // TODO: Streamline the API here.unwrap()
        let callee = self
            .module
            .declare_function(&name, Linkage::Import, &sig)
            .expect("problem declaring function");

        let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

        let mut arg_values = Vec::new();
        for arg in args {
            arg_values.push(arg.0)
        }

        let call = self.builder.ins().call(local_callee, &arg_values);

        self.builder.inst_results(call)[0]
    }

    fn translate_global_data_addr(&mut self, name: String) -> Value {
        let sym = self
            .module
            .declare_data(&name, Linkage::Export, true, false)
            .expect("problem declaring data object");

        let local_id = self.module.declare_data_in_func(sym, self.builder.func);

        let pointer = self.module.target_config().pointer_type();
        let ptr = self.builder.ins().symbol_value(pointer, local_id);
        self.builder
            .ins()
            .load(self.int, MemFlags::trusted(), ptr, Offset32::new(0))
    }
}
