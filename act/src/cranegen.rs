use std::{collections::BTreeSet, convert::identity, fs::File, io::Write, iter};

use codegen::{ir::immediates::Offset32, write_function};
use cranelift::{
    module::{DataDescription, DataId, FuncId, Linkage, Module, ModuleError},
    object::{ObjectBuilder, ObjectModule},
    prelude::*,
};
use im::HashMap;
use isa::CallConv;

use crate::{
    cst::{Cst, Expr, Statement},
    frontend::cst,
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
    daemons: Vec<Actor>,
    literal_counter: usize,
    globals: BTreeSet<String>,
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
            daemons: Vec::default(),
            literal_counter: 0,
            globals: BTreeSet::default(),
            debug: false,
        }
    }
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
        for a in &cst {
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

        for (idx, a) in cst.into_iter().enumerate() {
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
        // Our toy language currently only supports I64 values, though Cranelift
        // supports other types.
        let int = self.module.target_config().pointer_type();

        for _p in &params {
            self.ctx.func.signature.params.push(AbiParam::new(int));
        }

        // Our toy language currently only supports one return value, though
        // Cranelift is designed to support more.
        self.ctx.func.signature.returns.push(AbiParam::new(int));

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
        };

        let _ = stmts
            .into_iter()
            .map(|s| trans.translate_stmt(s))
            .any(identity);

        trans
            .builder
            .append_block_params_for_function_returns(ret_block);

        trans.builder.switch_to_block(ret_block);
        let ret_param = trans.builder.block_params(ret_block)[0];

        trans.builder.ins().return_(&[ret_param]);

        trans.builder.seal_block(ret_block);

        //let return_value = trans.translate_call(String::from("make_undefined"), vec![]);

        //trans.builder.ins().jump(ret_block, &[return_value]);

        // Tell the builder we're done with this function.
        if self.debug {
            let mut s = String::new();
            write_function(&mut s, &trans.builder.func).unwrap();
            println!("{s}");
        }

        trans.builder.finalize();
        Ok(())
    }
}

fn infix_func_name(op: InfixToken) -> String {
    match op {
        InfixToken::Plus => "eval_plus",
        InfixToken::Minus => "eval_minus",
        InfixToken::And => "eval_and",
        InfixToken::Or => "eval_or",
        InfixToken::GE => "eval_ge",
        InfixToken::LE => "eval_le",
        InfixToken::Greater => "eval_greater",
        InfixToken::Lesser => "eval_lesser",
        InfixToken::Equal => "eval_equals",
        InfixToken::Mul => "eval_mul",
        InfixToken::Div => "eval_div",
        InfixToken::Assign => panic!(),
    }
    .to_string()
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

        self.translate_call(name, vec![init_ptr, update_ptr, pid_slot_addr]);
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
                let runtime = self.translate_expr(Expr::Symbol(String::from("RUNTIME")));

                self.translate_call(
                    String::from("send_actor"),
                    vec![runtime, destination, value],
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

                let rt = self.translate_expr(Expr::Symbol("RUNTIME".to_string()));
                let condition = self.translate_expr(condition);

                let cond = self.translate_call("eval_conditional".to_string(), vec![rt, condition]);

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
                let rt = self.translate_expr(Expr::Symbol("RUNTIME".to_string()));
                let other_args = args.into_iter().map(|arg| self.translate_expr(arg));
                let args = iter::once(rt).chain(other_args).collect();

                let _ = self.translate_call(func_name, args);
                false
            }
        }
    }

    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
            Expr::Number(f) => {
                let imm = self.builder.ins().f64const(f);

                self.make_number(imm)
            }
            Expr::String(s) => self.translate_string(s),
            Expr::Symbol(name) => self.translate_symbol(name),
            Expr::Bool(b) => {
                let imm = if b { 1 } else { 0 };
                let imm = self.builder.ins().iconst(self.int, imm);
                let rt = self.translate_expr(Expr::Symbol(String::from("RUNTIME")));

                self.translate_call(String::from("make_gc_bool"), vec![rt, imm])
            }
            Expr::Infix { left, op, right } => {
                let args = vec![
                    self.translate_expr(Expr::Symbol(String::from("RUNTIME"))),
                    self.translate_expr(*left),
                    self.translate_expr(*right),
                ];
                let name = infix_func_name(op);
                self.translate_call(name, args)
            }
        }
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
            self.translate_expr(Expr::Symbol(String::from("RUNTIME"))),
            ptr,
        ];

        let name = String::from("make_gc_string");

        self.translate_call(name, args)
    }

    fn make_number(&mut self, number: Value) -> Value {
        let mut sig = self.module.make_signature();
        sig.call_conv = CallConv::SystemV;
        let rt = self.translate_expr(Expr::Symbol(String::from("RUNTIME")));

        // Add a parameter for each argument.
        sig.params.push(AbiParam::new(self.int));
        sig.params.push(AbiParam::new(types::F64));

        // For simplicity for now, just make all calls return a single I64.
        sig.returns.push(AbiParam::new(self.int));

        // TODO: Streamline the API here.unwrap()
        let callee = self
            .module
            .declare_function("make_gc_number", Linkage::Import, &sig)
            .expect("problem declaring function");

        let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

        let call = self.builder.ins().call(local_callee, &[rt, number]);

        self.builder.inst_results(call)[0]
    }

    fn translate_call(&mut self, name: String, args: Vec<Value>) -> Value {
        let mut sig = self.module.make_signature();
        sig.call_conv = CallConv::SystemV;

        // Add a parameter for each argument.
        for _arg in &args {
            sig.params.push(AbiParam::new(self.int));
        }

        // For simplicity for now, just make all calls return a single I64.
        sig.returns.push(AbiParam::new(self.int));

        // TODO: Streamline the API here.unwrap()
        let callee = self
            .module
            .declare_function(&name, Linkage::Import, &sig)
            .expect("problem declaring function");

        let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

        let mut arg_values = Vec::new();
        for arg in args {
            arg_values.push(arg)
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
