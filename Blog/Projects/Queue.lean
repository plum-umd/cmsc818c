import VersoBlog
import Queue

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "."

#doc (Page) "Project 2: A Bounded Queue" =>

Implementing a component correctly often means preserving a simple meaning through a less
obvious representation. In this project, a list specifies a first-in, first-out queue, while
a circular buffer stores its contents in a fixed-size array. Your task is to connect those
two views with proofs, then preserve that connection across a sequence of calls.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/queue) contains
the reference model, circular-buffer operations, executable checks, and proof obligations.
No allocator solution is needed to start this project.

# Build and Explore

From the repository root:

```
cd projects/queue
lake build
```

Open this directory as a Lean project. The supplied modules are:

- `Queue/Model.lean`: commands, replies, a list-based semantics, an executable reference,
  and proofs connecting that reference to the semantics.
- `Queue/Buffer.lean`: the circular-buffer representation, its operations, and trace runners.
- `Queue/Exercises.lean`: propositions stating the obligations you will prove.
- `Queue/Support.lean`: a supplied modular-arithmetic lemma for the wraparound argument.
- `Checks.lean`: executable examples covering wraparound, duplicates, stored zero, and failure.

The starter builds, but the propositions in `Queue/Exercises.lean` are not supplied proofs.
Your core work is to establish the representation and refinement results described below.
Additional implementation and framing tasks are optional extensions. The companion
[queue warm-up](notes/2026-11-7-warmup-a-verified-queue-from-semantics-to-risc/),
[representation-invariants](notes/2026-11-7-representation-invariants/), and
[refinement](notes/2026-11-7-refinement-and-simulation/) notes provide worked guidance.
Use that guidance to understand the argument and explain the proofs you construct.

# Model.lean: Describe the Behavior First

## Commands and Replies

```anchor queueInterface (module := Queue.Model)
abbrev Word := UInt64

inductive Command where
  | push (value : Word)
  | pop
  deriving Repr, DecidableEq

inductive Reply where
  | ok
  | full
  | empty
  | value (word : Word)
  deriving Repr, DecidableEq
```

`push` appends a value; `pop` removes the oldest value. Payloads are unsigned 64-bit words.
Every word is a valid payload, including zero, and duplicates are allowed. A separate reply
constructor distinguishes empty queues from successful pops. A full queue rejects a push
without discarding an existing element.

## List Semantics

```anchor queueStep (module := Queue.Model)
def Valid (capacity : Nat) (queue : List Word) : Prop := queue.length ≤ capacity

inductive Step (capacity : Nat) : List Word → Command → Reply → List Word → Prop where
  | push (room : queue.length < capacity) :
      Step capacity queue (.push value) .ok (queue ++ [value])
  | full (full : queue.length = capacity) :
      Step capacity queue (.push value) .full queue
  | pop : Step capacity (value :: rest) .pop (.value value) rest
  | empty : Step capacity [] .pop .empty []
```

The list records elements in FIFO order. `Step capacity queue command reply next` states
which results are permitted. The rules mention neither array slots nor physical indices.
Notice that a full push and an empty pop both leave the abstract state unchanged.

`run` computes the result described by this relation:

```anchor queueRun (module := Queue.Model)
def run (capacity : Nat) (queue : List Word) : Command → Reply × List Word
  | .push value =>
      if queue.length < capacity then (.ok, queue ++ [value]) else (.full, queue)
  | .pop =>
      match queue with
      | [] => (.empty, [])
      | value :: rest => (.value value, rest)
```

The module supplies `run_sound`, `step_run`, and `step_deterministic`. Read their statements
before starting: they establish that the executable reference agrees with the semantics and
that a step has a unique result. They do not establish anything about the circular buffer.

# Buffer.lean: Change the Representation

## Physical Storage and Logical Contents

```anchor bufferState (module := Queue.Buffer)
structure State where
  slots : Array Word
  head : Nat
  count : Nat
  deriving Repr, DecidableEq

/-- Storage size is fixed by the client, rather than duplicated in runtime metadata. -/
def Valid (capacity : Nat) (buffer : State) : Prop :=
  0 < capacity ∧ buffer.slots.size = capacity ∧
    buffer.head < capacity ∧ buffer.count ≤ capacity

/-- Total observation; validity will establish that occupied reads are in bounds. -/
def contents (slots : Array Word) (head count : Nat) : List Word :=
  (List.range count).map fun i => slots[(head + i) % slots.size]?.getD 0

def view (buffer : State) : List Word := contents buffer.slots buffer.head buffer.count

def Rep (capacity : Nat) (buffer : State) (queue : List Word) : Prop :=
  Valid capacity buffer ∧ view buffer = queue
```

`slots` holds the payloads, `head` identifies the oldest occupied slot, and `count` records
the number of occupied slots. The client fixes capacity; a valid buffer has exactly that many
slots. Every slot can be used. The count distinguishes a full queue from an empty one even
when their head indices coincide.

`view` is the abstraction function. Logical element `i` lives in physical slot
`(head + i) % slots.size`, for `i < count`. Unoccupied slots may retain old values and do not
contribute to the view. `Rep` combines the representation invariant with the equation saying
which abstract queue the buffer represents.

Optional array reads and `.getD 0` make `view` a total function, including on invalid states.
This is not permission to treat invalid accesses as valid zero-valued elements. Your proof
must show that occupied reads are in bounds whenever the representation invariant holds.

## Operations

```anchor bufferOperations (module := Queue.Buffer)
def empty (capacity : Nat) : State := ⟨Array.replicate capacity 0, 0, 0⟩

def push (buffer : State) (value : Word) : Reply × State :=
  if buffer.count < buffer.slots.size then
    (.ok, { buffer with
      slots := buffer.slots.setIfInBounds ((buffer.head + buffer.count) % buffer.slots.size) value
      count := buffer.count + 1 })
  else (.full, buffer)

def pop (buffer : State) : Reply × State :=
  if buffer.count = 0 then (.empty, buffer)
  else
    (.value (buffer.slots[buffer.head]?.getD 0),
      { buffer with head := (buffer.head + 1) % buffer.slots.size, count := buffer.count - 1 })

def run (buffer : State) : Command → Reply × State
  | .push value => push buffer value
  | .pop => pop buffer
```

Successful push writes at the logical end and increments the count. Successful pop advances
the head and decrements the count; it does not erase the payload. Full and empty failures
preserve the entire concrete state. Proving the reply correct is only part of refinement:
you must also prove that the new view is correct and the next state remains valid.

# Try a Wrapped Buffer

```leanInit queueProject
```

```lean queueProject
open Course.Queue

def sample : Buffer.State := ⟨#[9, 99, 7, 8], 2, 3⟩

example : Buffer.view sample = [7, 8, 9] := by decide
example : Buffer.push sample 10 = (.ok, ⟨#[9, 10, 7, 8], 2, 4⟩) := by decide
example : Buffer.pop (Buffer.push sample 10).2 =
    (.value 7, ⟨#[9, 10, 7, 8], 3, 3⟩) := by decide
```

The unused slot containing 99 initially has no abstract meaning. Pushing 10 overwrites it,
and the buffer becomes full. Popping then returns 7, rather than the first element in physical
array order. Use the editor to inspect these examples and predict the result of another pop.

# From One Call to Many

```anchor bufferTrace (module := Queue.Buffer)
def runTrace (buffer : State) : List Command → List Reply × State
  | [] => ([], buffer)
  | command :: commands =>
      let (reply, next) := run buffer command
      let (replies, final) := runTrace next commands
      (reply :: replies, final)
```

`runTrace` records every reply and threads the concrete state through the calls.
`referenceTrace` does the same with the list model. A trace-refinement theorem must show
agreement of replies and final logical contents, along with validity of the final buffer.
The invariant produced by one call is what permits the induction to continue at the next.

```lean queueProject
example :
    let result := Buffer.runTrace (Buffer.empty 2)
      [.push 7, .push 9, .push 11, .pop, .push 0, .pop, .pop, .pop]
    (result.1, Buffer.view result.2) =
      ([.ok, .ok, .full, .value 7, .ok, .value 9, .value 0, .empty], []) := by decide
```

# The Main Correctness Goal

The main goal is a simulation statement relating the concrete buffer to the specification:

```anchor queueSimulation (module := Queue.Exercises)
def Simulation : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (queue : List Word) (command : Command),
    Buffer.Rep capacity buffer queue →
      ∃ nextQueue : List Word,
        Step capacity queue command (Buffer.run buffer command).1 nextQueue ∧
        Buffer.Rep capacity (Buffer.run buffer command).2 nextQueue
```

Start with a buffer representing an abstract queue. Execute a concrete command. The theorem
must produce a next abstract queue such that the concrete reply is allowed by `Step` and the
next buffer represents that next queue. `Rep` includes validity, so the result provides the
representation invariant needed for the next call as well as the correct logical contents.

One way to reach that theorem is through equality with the executable reference:

```anchor queueRefinement (module := Queue.Exercises)
def Refinement : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (command : Command),
    Buffer.Valid capacity buffer →
      ((Buffer.run buffer command).1, Buffer.view (Buffer.run buffer command).2) =
        run capacity (Buffer.view buffer) command
```

This equality is a useful intermediate result. Combine it with preservation and the supplied
connection between the reference function and `Step` to derive the relational statement:

```anchor queueSimulationTransfer (module := Queue.Exercises)
def SimulationFromRefinement : Prop :=
  Preservation → Refinement → Simulation
```

Prove this implication and apply it to your theorems. Explain why the equality alone does not
establish `Simulation`: it describes the concrete view and reply, but the next state's
representation invariant must also be established.

# A Supplied Lemma for Wraparound

The arithmetic should support the refinement argument rather than obscure it. The starter
supplies this lemma in `Course.Queue.Support`:

```anchor slotInjectivity (module := Queue.Support)
/-- Within one turn of a nonempty ring, different logical positions use different slots. -/
theorem slot_injective {head capacity i j : Nat}
    (headBound : head < capacity) (iBound : i < capacity)
    (jBound : j < capacity)
    (same : (head + i) % capacity = (head + j) % capacity) : i = j := by
  rw [Nat.add_mod_eq_ite, Nat.add_mod_eq_ite] at same
  simp only [Nat.mod_eq_of_lt headBound, Nat.mod_eq_of_lt iBound,
    Nat.mod_eq_of_lt jBound] at same
  split at same <;> split at same <;> omega
```

Use it to show that a push into logical position `count` cannot overwrite an existing element
at logical position `i < count`. First extract the head and capacity bounds from `Buffer.Valid`.
For a successful push, there is room, so `count < capacity`. If the two physical slots were
equal, the lemma would force `i = count`, contradicting `i < count`. This is the bridge from
an array update to preservation of all existing list elements.

Read the lemma's hypotheses and explain where each comes from in the push proof. You may use
the supplied theorem without reconstructing its modular-arithmetic proof.

# Core Assignment

1. *Initialization and observation.* Prove `Exercises.Initialization` and
   `Exercises.OccupiedReads`. Establish that `view buffer` has length `buffer.count`.
   Explain why positive capacity is required for the representation invariant.
2. *Preserve the representation.* Prove `Exercises.Preservation`. Identify which fields
   change in each operation and establish the next head and count bounds.
3. *Connect the meanings.* Prove `Exercises.Refinement`, then prove
   `Exercises.SimulationFromRefinement` and derive `Exercises.Simulation`. A successful push
   must preserve all existing logical elements and append exactly one new element; a
   successful pop must remove exactly the first element. Use the supplied slot-injectivity
   lemma. Account for full and empty replies as well as successful operations.
4. *Compose the guarantees.* Prove `Exercises.TraceRefinement` by induction over commands.
   Derive a result for traces starting from `Buffer.empty capacity`. Explain how single-call
   correctness and preservation justify continuing the argument after each command.

Create `Queue/Solution.lean`, import `Queue.Exercises`, and import your solution from
`Checks.lean`. Keep the starter definitions and exercise propositions fixed. Do not import
the website's worked proof modules into your solution.

Submit the proofs and a short write-up explaining the abstraction function, the distinction
between `Refinement` and `Simulation`, and the induction hypothesis used for traces. Include
one wrapped-buffer example and explain why pushing does not overwrite an occupied element.
The notes provide worked arguments, so proof checking alone is not evidence that you understand
the development: your explanation should identify the critical invariants, lemma applications,
and assumptions, including how you evaluated suggestions from an agent.

# Optional Extensions

These tasks go beyond the core assignment. They provide opportunities to apply the reasoning
to new code and are useful evidence of independent understanding.

1. *Preserve unrelated state.* Prove `Exercises.FailureAtomicity` and `Exercises.PopFrame`.
   Explain the difference between preserving all array contents and preserving the abstract
   queue contents. Extend the push proof with a frame statement for every other physical slot.
2. *Implement a variation.* Write an alternative pop that advances the head with a conditional
   wrap at capacity instead of `%`. Give it its own name and prove that it agrees with
   `Buffer.pop` on valid buffers, including capacity one. Transfer the simulation guarantee
   without repeating the entire queue-correctness argument. Keep the failure behavior and
   payload-frame property unchanged. Include the new code, proofs, and boundary tests in
   your submission, and explain which existing results you reused.

The starter's `Audit.lean` demonstrates how to inspect the assumptions of supplied theorems:

```
lake env lean Audit.lean
```

Add your own theorems to the audit. Use agents to search for library lemmas and propose
proof steps, but ask them to explain the relevant invariant before attempting a theorem.
Reject attempts to exclude wraparound, forbid duplicate values, reserve a payload value
for errors, or weaken the required conclusions. Do not discharge obligations with new
axioms, `sorry`, or `admit`.

# Scope and Later Connections

Calls are sequential, and the client has exclusive access to the state. Head indices and
counts use mathematical natural numbers. The payloads have a fixed width, but the metadata
does not yet have machine-overflow behavior. A later machine implementation must establish
representability and handle address calculations explicitly.

This queue is an ordinary bounded FIFO: it allows duplicates and reports exhaustion.
Its contract is deliberately smaller than the scheduler queue in PL/OS. The transferable
ideas are representation invariants, refinement, framing, and composition, rather than a
claim that this component can be dropped into the operating system unchanged.
