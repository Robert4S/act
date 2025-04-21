# Compiler and runtime for 'Act' programming language
# Dependencies
For simplicity, the Gnu C Compiler is used to lower and link the emitted assembly, so it is a requirement. The rust toolchain (cargo) is also required to build the compiler and runtime library.
## Model of computation
The act programming language follows the actor model purely. There are no functions or objects, and the main building block for computation is an actor.
## Memory model
Memory for programs written in Act is automatically managed by a (slow) tracing garbage collector. The garbage collector cannot run at the same time as any generated code, to prevent race conditions.
## What is an actor
An actor encapsulates an initialiser function, and an updator function that will produce a new state for the actor given a message from its mailbox.
Actors run in their own threads, and do not "share" memory with other actors. They can send messages to other actors, which will be placed in their mailbox, and popped off so that the other actor may produce a new state for itself. These mailboxes replace the call stack traditionally found in Procedural, Functional, and Object Oriented languages
A program is finished when all actors in it are finished, and actors signal that they are finished by returning as their new state the string "I am done with my work here". Whenever an actor finishes, it's last state before finishing will be printed along with its PID (process identifier).
## What can an actor do
The Initialiser and Updater functions for actors are collections of statements. The set of possible statements are as follows:
### If condition
Consists of a boolean value, a branch to follow if the boolean is true, and optionally, a branch to follow if it is not true. Each of these branches are also collections of statements.
#### Syntax:
```
if (condition) { 
    (semicolon separated statements)
} else { 
    (semicolon separated statements) 
}
```
*Note:* If statements must be followed by a semicolon, just like any other statement
### Assignment
Assignments are for assigning the value of the expression on the right hand side to the variable name on the left hand side
#### Syntax:
`variable_name: Type = expression`
### Send
An actor can send a value as a message to another actor, and this message will be added to the other actor's message queue. Any expression can be sent as a message
#### Syntax:
`send(actor, message)`, where the first argument expression will be validated to be a process ID at runtime
### Actor creation statement
Actors can create other actors dynamically, and the name used for the creation of this actor will become a variable with the value of the spawned actor's PID.
#### Syntax:
```
actor my_actor {
    state state_name: StateType;

    initialiser {
        (semicolon separated statements)
    } 

    update (arg_name: ArgType) {
        (semicolon separated statements)
    }
}
```
### Intrinsic statement
This provides a way for actors to sequentially call rust functions that must be linked in to the emitted object file. The arguments given to the intrinsic must be the unmangled name of the stub to be called, and a list of runtime values to be passed to it. The rust stub must accept a reference to the runtime as its first argument, and the rest of it's argument list must be solely GC pointers. If the arity of the stub does not align with what has been passed using the intrinsic statement, the resulting behavior is undefined.
#### Syntax:
`intrinsic(stub_name, "Hello world", 5, 10.2, true)` \
This expects a rust function with the following signature to be linked in
```rust
extern "C" fn stub_name(rt: &RT, arg1: Gc, arg2: Gc, arg3: Gc, arg4: Gc)
```
# Examples
In this repository you will find the factorial.act file. Run the build script in the repository root, then simply run \
`act -f ./factorial.act` \
And a binary named factorial will be emitted, along with a factorial.S assembly file with the emitted assembly.
