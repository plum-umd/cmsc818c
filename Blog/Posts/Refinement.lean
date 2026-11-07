import VersoBlog
import Blog.Examples.CircularBufferChecks

open Verso Genre Blog

#doc (Post) "Refinement and Simulation" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

A circular buffer and a list can implement the same queue without having equal internal
states. Refinement makes that claim precise: concrete execution must produce behavior
permitted by an abstract specification.

We now have an [abstract step relation](notes/2026-11-7-operational-semantics/), a checked
[list implementation](notes/2026-11-7-an-executable-specification/), and a checked
[circular buffer](notes/2026-11-7-representation-invariants/). The refinement proofs live
in `Blog/Examples/CircularBuffer.lean` and are part of the website build.

# State the Relation Before the Proof

`Buffer.Rep capacity buffer queue` asserts that the buffer is valid and its view is `queue`.
The concrete function `Buffer.run` computes a reply and next buffer for one command.
The abstract function `Course.Queue.run` computes a reply and next list.

Their operation-level agreement theorem has this checked form:

```leanInit refinement
```

```lean refinement
open Course.Queue

example (valid : Buffer.Valid capacity buffer) (command : Command) :
    ((Buffer.run buffer command).1, Buffer.view (Buffer.run buffer command).2) =
      Course.Queue.run capacity (Buffer.view buffer) command := by
  exact Buffer.run_refines valid command
```

The pair compares both the reply and the logical contents of the next state. Internal array
positions may differ from list positions; the observable result must agree. Initialization
and preservation are separate theorems establishing and maintaining the representation.

# One Operation, Four Cases

For successful push, the representation invariant equates array size with capacity, while
the view's length equals the count. The concrete space check therefore agrees with the
abstract space check. `Buffer.contents_push` supplies the new list `queue ++ [value]`.

The full case returns `full` and preserves the entire buffer. Successful pop uses
`Buffer.contents_pop` to identify the returned first element and the new logical tail.
Empty pop returns `empty` and preserves state. These four cases prove `Buffer.push_refines`
and `Buffer.pop_refines`; dispatching on the command proves `Buffer.run_refines`.

The proofs apply to every valid buffer, including wrapped states with arbitrary unused slot
values. They do not assume that the queue has only been used in a particular example trace.

# Connect to the Transition Relation

Agreement with the reference function connects to the independently stated semantics through
`step_iff_run`. Here is the complete proof of the simulation conclusion, using the checked
component results:

```lean refinement
example (rep : Buffer.Rep capacity buffer queue) (command : Command) :
    Step capacity queue command (Buffer.run buffer command).1
        (Buffer.view (Buffer.run buffer command).2) ∧
      Buffer.Rep capacity (Buffer.run buffer command).2
        (Buffer.view (Buffer.run buffer command).2) := by
  constructor
  · apply (step_iff_run (Buffer.rep_valid rep)).2
    rw [← rep.2]
    exact (Buffer.run_refines rep.1 command).symm
  · exact ⟨Buffer.run_valid rep.1 command, rfl⟩
```

The first conjunct supplies the matching abstract transition with exactly the concrete reply.
The second supplies a related next buffer. The new abstract state is its view, so that part
of the representation relation holds by reflexivity. The library names this result
`Buffer.run_simulates`.

# Avoid a Vacuous Simulation

An implication saying that every completed concrete operation matches an abstract step would
also hold for an implementation that never completes any operation. Here the concrete
operations are total Lean functions: every command computes a result, and Lean accepts their
terminating definitions. The simulation theorem then covers that actual computed result.

Similarly, `Buffer.empty_rep` supplies real related starting states for every positive capacity.
The representation relation cannot satisfy the development merely by being false everywhere.
For machine code, reaching a return point without unexpected faults will require a new
execution theorem; totality of these Lean functions does not establish that machine claim.

# Lift the Result to a Client Trace

`Buffer.runTrace` runs a finite list of commands, threading the concrete state through calls
and recording every reply. `Buffer.referenceTrace` does the same with the abstract function.
Induction over the commands lifts one-operation agreement to whole-trace agreement:

```lean refinement
example (valid : Buffer.Valid capacity buffer) (commands : List Command) :
    ((Buffer.runTrace buffer commands).1,
      Buffer.view (Buffer.runTrace buffer commands).2) =
      Buffer.referenceTrace capacity (Buffer.view buffer) commands := by
  induction commands generalizing buffer with
  | nil => rfl
  | cons command commands ih =>
    have one := Buffer.run_refines valid command
    have rest := ih (Buffer.run_valid valid command)
    simp only [Buffer.referenceTrace, Buffer.runTrace]
    rw [← one]
    simp only
    rw [← rest]
```

The induction hypothesis must apply to the next buffer, not just the initial one. Generalizing
`buffer` permits that change, and preservation establishes the premise needed to invoke it.
`Buffer.trace_valid` separately proves validity of the final buffer. `Buffer.initialized_trace`
combines both results for runs starting empty.

Here is a concrete trace containing duplicate values, a rejected push, wraparound, and zero:

```lean refinement
example :
    let result := Buffer.runTrace (Buffer.empty 2)
      [.push 7, .push 7, .push 9, .pop, .push 0, .pop, .pop, .pop]
    (result.1, Buffer.view result.2) =
      ([.ok, .ok, .full, .value 7, .ok, .value 7, .value 0, .empty], []) := by decide
```

This example helps us inspect the contract. The general trace theorem establishes agreement
for every finite command list, not just the traces in the examples.

# Relate Different Execution Granularities

At the RISC level, one interface operation takes multiple instruction steps. A new relation
will connect registers and memory to the buffer state. Its execution theorem must identify
entry conditions, a finite execution to the return point, the reply, and the next represented
buffer, together with memory and register preservation.

Compose the machine-to-buffer relation with the buffer-to-list relation through an intermediate
buffer. Machine execution supplies a buffer operation; the theorem above supplies an abstract
step. Our current counts and indices use natural numbers, so finite-width arithmetic and
address bounds remain obligations for that next implementation level.

The same method applies to PL/OS components, but the client contract still matters. Our
bounded FIFO permits duplicate values and lacks removal; PL/OS's scheduler queue suppresses
duplicates and supports removal. This proof does not establish that stronger contract.

# Exercise

Explain why agreement on the final queue alone would miss an implementation returning wrong
status codes. Then examine `Buffer.initialized_trace`: which conjunct lets a caller safely
continue with another command? What new assumptions would be needed if another thread could
mutate the buffer between its metadata check and its array access?

Return to the [warm-up](notes/2026-11-7-warmup-a-verified-queue-from-semantics-to-risc/) to see
where the checked buffer fits. The [table of contents](notes/) lists the next machine-level
implementation topics.
