import VersoBlog

open Verso Genre Blog

#doc (Post) "Warm-Up: A Verified Queue from Semantics to RISC" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

Before tackling an operating system, we will work through a small system whose entire
behavior we can understand: a bounded first-in, first-out queue. We will specify its
behavior, implement it at two levels, and connect those implementations with proofs.
This post outlines the exercise and the questions each stage should answer.

The companion posts on [representation invariants](notes/2026-11-7-representation-invariants/)
and [refinement](notes/2026-11-7-refinement-and-simulation/) now include a checked Lean
circular buffer and proofs connecting its operations and client traces to the list model.
The RISC implementation and machine-level proofs remain the next stage.

A queue is small enough to study on its own, but it raises real systems questions about
finite storage, representation, memory access, and failure. It also connects directly to
[PL/OS](notes/2026-11-7-plos-from-a-lean-prototype-to-verified-risc-code/), whose scheduler
maintains a queue of runnable processes.

# 1. Decide What the System Does

Fix a positive capacity `C`. Queue elements are unsigned machine words; repeated values
are allowed. The interface has two commands:

- `push(x)` appends `x` if there is room, returning `ok`. If the queue is full, it returns
  `full` and leaves the queue unchanged.
- `pop` removes and returns the oldest element. If the queue is empty, it returns `empty`
  and leaves the queue unchanged.

Errors are part of the specification. A full queue must not silently overwrite its oldest
element, and an empty queue must not return an arbitrary word. The result needs a separate
status: every word, including zero, is a valid element.

We will initially assume sequential calls, exclusive access to the queue's storage, and no
interrupts during an operation. These assumptions define the first problem we will solve.
Concurrent access would require a stronger specification and additional reasoning.

# 2. Give the Commands a Semantics

An abstract state is a list `q` of words satisfying `length(q) <= C`. Write
`Step(q, command, reply, q')` to mean that the command may return `reply` and leave abstract
state `q'`. Its rules are:

- If `length(q) < C`, then `push(x)` returns `ok` and the next state is `q ++ [x]`.
- If `length(q) = C`, then `push(x)` returns `full` and the next state is `q`.
- If `q = x :: rest`, then `pop` returns `value(x)` and the next state is `rest`.
- If `q = []`, then `pop` returns `empty` and the next state is `[]`.

These rules are an operational semantics: they describe how commands change state.
They also serve as our behavioral specification. They mention no registers, pointers,
array slots, or instruction sequences.

Extending one step to a sequence of steps gives semantics to a client program. With capacity
two, pushing 7, pushing 9, pushing 11, and popping three times must produce replies
`ok`, `ok`, `full`, `value(7)`, `value(9)`, and `empty`.

First proof goals: every valid state and command have exactly one permitted reply and next
state, and every permitted step preserves the capacity bound.

# 3. Build a High-Level Executable Model

Implement the interface in Lean using a list and an explicit result type. Run short command
sequences, including the example above. This gives us an executable reference that is easy
to inspect and useful for testing later implementations.

Then prove both directions of the connection: the function's result satisfies `Step`, and
every result permitted by `Step` is the result computed by the function. The definitions
should make these proofs small. The exercise is to see the distinction between a relation
describing permitted behavior and a function computing that behavior.

Tests help us discover mistakes and clarify examples. The theorem covers all valid queues
and commands, rather than only the command sequences we happened to run.

# 4. Change the Representation

Implement a circular buffer with `C` slots, a head index `h`, and a count `n`. Its invariant
requires exactly `C` slots, `0 <= h < C`, and `0 <= n <= C`.

The abstraction function reads the occupied slots in logical order: the element at logical
position `i` is in physical slot `(h + i) mod C`, for `0 <= i < n`. Unoccupied slots can
contain old values; they contribute nothing to the abstract queue.

On a successful push, write the new value to slot `(h + n) mod C` and increment the count.
On a successful pop, read slot `h`, advance the head modulo `C`, and decrement the count.
Check full and empty conditions before touching a payload slot.

Now prove representation preservation and refinement. If a valid buffer represents `q`,
performing a command must return the abstract reply and leave a valid buffer representing
the abstract next state. The concrete buffer does not have to resemble a list internally;
the abstraction function explains what it means.

Useful tests include capacity one, wraparound, alternating pushes and pops, duplicate values,
and operations on full and empty queues. Comparing replies and abstract states against the
reference model makes these differential tests.

# 5. Implement the Operations for a RISC Machine

Choose a small, explicit instruction-set model and calling convention. Give the buffer a
memory layout: fields for the head and count, followed by fixed-width payload slots. Specify
which registers hold arguments and results, which registers may be overwritten, and where
execution returns.

This introduces a second representation relation, connecting registers and memory to the
circular-buffer state. Its preconditions must establish alignment, allocated storage,
non-overlapping code and data, and valid metadata. They must also ensure that capacities,
offsets, and address calculations fit the machine representation.

Mathematical arithmetic needs particular care. Computing `h + n` in a machine register can
overflow before a remainder operation. One option is to restrict capacity enough that the
sum fits; another is to implement wraparound without forming an overflowing sum. We must
choose an approach and prove its obligations.

For each routine, the target theorem should say: from a machine state meeting the
preconditions, execution reaches the designated return point in finitely many steps,
returns the specified reply, and represents the correct next queue. It must also preserve
the required registers and memory outside its allowed footprint. Merely showing that a
routine is correct _if_ it returns leaves termination and faults unresolved.

Use an emulator or executable instruction semantics to run the same example traces.
The machine proof must concern the instructions that actually execute; a proof about
high-level pseudocode alone does not establish correctness of a separately written routine.

# 6. Connect the Proofs

The proof has three levels: abstract queue behavior, circular-buffer operations, and machine
execution. A machine routine implements a buffer operation, and that operation implements an
abstract queue step. Composing the connections gives an end-to-end statement about replies
and queue contents.

Prove the result for sequences of calls as well as individual calls. Preservation establishes
the next call's representation invariant; a client must still supply valid arguments and
respect the calling convention and exclusive-access assumptions. Internal instructions may
take many steps for one abstract command. Refinement relates those different granularities
of execution.

Keep a record of the trusted boundary: the selected instruction semantics, memory assumptions,
and any connection between modeled instructions and an emitted executable. Checking a proof
against a machine model does not establish that every physical platform implements that model.

# How We Will Use Agents

Use a coding agent to help set up the Lean project, implement the reference model, generate
test traces, find lemmas, and propose proofs. Give it one stage at a time and have it explain
the invariant and intended theorem before filling in a proof.

Review the specification independently. In particular, reject attempts to avoid hard cases
by changing the full-queue behavior, excluding wraparound, assuming the routine's result,
or silently adding preconditions. Explicit design decisions are welcome; hidden changes to
the problem are not. Check the Lean files and inspect proofs for unfinished placeholders
and unapproved assumptions.

The finished warm-up should contain the semantics, executable models, RISC routines, tests,
and checked refinement proofs, together with a short explanation of the assumptions. These
are proposed deliverables for the exercise, not artifacts supplied by this outline.

# Connecting Back to the Operating System

The same workflow applies to process tables, channel-handle tables, and communication queues:
describe their meaning, choose a representation, implement operations, and prove that the
operations preserve that meaning and the surrounding state.

Our warm-up queue is deliberately simpler than PL/OS's scheduler queue. The current scheduler
queue suppresses duplicate process identifiers and supports removal; this bounded FIFO
allows duplicates and reports capacity exhaustion. Integrating it would require extending
the implementation and proving the actual scheduler contract, including a capacity policy.

That distinction is part of the lesson. A component is reusable when its proved contract
meets its client's requirements. Starting with a small queue lets us practice establishing
that connection before we attempt it across an operating system.
