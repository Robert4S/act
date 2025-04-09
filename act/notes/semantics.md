# Actors
Actors are created strictly when an <actor> statement is encountered. The name expression is stored in a global actor table with the associated actor.

# Global actor table
Once an actor is created, it is permanently stored in the global actor table. This means that it's mailbox and state will forever be GC roots. Actors run in separate green threads, constantly dequeueing values from its mailbox and updating it's state with it's update function.
If a GC pause flag is activated, green threads will not continue to the next dequeue from their mailbox, and instead finish the current computation, and then wait until the flag is deactivated.

# Garbage collector
The garbage collector will run in a separate OS thread. When a GC cycle is desired, a "pause" flag will be activated, and when all actors have halted, a mark and sweep collection cycle will be triggered. Any values in the mailboxes of actors in the global actor table are GC roots, and all values in the state sections of actors will also be GC roots. Because there are no functions, and no updator will be running while a GC cycle is active, regular assignments and function arguments will not be treated as GC roots.
