import VersoBlog
import Blog.Examples.Queue

open Verso Genre Blog

#doc (Post) "Invariants and Induction" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

A specification can describe one operation without proving anything about a whole run.
To reason about arbitrarily long executions, we use an invariant: a property established
initially and preserved by every permitted step.

For our [queue semantics](notes/2026-11-7-operational-semantics/), the first invariant is
`Valid C q`, defined as `q.length <= C`.

# Initialization and Preservation

The empty queue is valid because zero is at most every natural-number capacity. Preservation
says that a step starting in a valid state ends in a valid state. Its proof follows the four
transition rules:

- Successful push appends one element. Its premise says the old length is strictly below
  capacity, so adding one stays within the bound.
- Full push leaves the list unchanged.
- Successful pop removes one element, so its length decreases.
- Empty pop leaves the empty list unchanged.

The shared model proves this as `step_preserves`. We can use it without inspecting which
rule produced the step:

```leanInit invariants
```

```lean invariants
open Course.Queue

example (valid : Valid capacity queue)
    (step : Step capacity queue command reply next) : Valid capacity next := by
  exact step_preserves valid step
```

A caller supplies validity and a transition; the theorem supplies validity of the result.
The two premises serve different purposes. The transition describes this operation, while
validity connects it to the state assumptions required for the execution as a whole.

# Define Reachability

A state is reachable if it is the empty initial queue or follows a reachable state by one
permitted transition. In Lean, the model records precisely those two constructors:

```lean invariants
inductive FromEmpty (capacity : Nat) : List Word → Prop where
  | initial : FromEmpty capacity []
  | next : FromEmpty capacity queue →
      Step capacity queue command reply next → FromEmpty capacity next
```

A proof of reachability contains a finite history of rule applications. Induction over that
proof gives a case for initialization and a case for extending an execution:

```lean invariants
example (reach : FromEmpty capacity queue) : Valid capacity queue := by
  induction reach with
  | initial => simp [Valid]
  | next _ step ih => exact step_preserves ih step
```

In the second case, `ih` is the induction hypothesis: the preceding reachable queue is valid.
Applying preservation to `ih` and the last step establishes the result. We never need to
know how many operations the client performed.

# An Invariant Must Be Strong Enough

A bound on queue length does not establish FIFO behavior. A stack also preserves that bound.
FIFO comes from the transition rules; capacity safety is one consequence we prove about them.
Do not substitute one property for the whole correctness claim.

Later, the circular-buffer representation will require several facts together: positive
capacity, the right array size, a head index in range, and a count at most capacity. A count
bound alone would allow an invalid head index and an out-of-range memory access.

Sometimes the property we want is too weak to prove inductively. We strengthen the invariant
with supporting facts needed by the next operation. Each additional clause needs its own
initialization and preservation argument. Adding the desired conclusion as an assumption
without establishing it does not solve the problem.

# Invalid States and Client Obligations

An arbitrary list may exceed capacity, even though no execution from empty creates it.
Reachability separates states the model can describe from states a valid run can visit.
At a machine boundary, the caller may be responsible for establishing a representation
invariant; later calls can reuse preservation to maintain it.

# Exercise

Suppose a buggy full-push operation overwrites the oldest element while keeping the length
unchanged. Does the capacity invariant detect the bug? Which part of the specification does?
Then propose an invariant for a circular buffer and explain why each clause is needed.

Next: [An Executable Specification](notes/2026-11-7-an-executable-specification/) turns the
rules into a function while preserving their meaning.
