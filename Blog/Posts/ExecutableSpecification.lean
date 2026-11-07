import VersoBlog
import Blog.Examples.Queue

open Verso Genre Blog

#doc (Post) "An Executable Specification" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

A transition relation describes permitted behavior. To run examples and compare implementations,
we also want a function that computes it. We will implement the queue using lists, then prove
that the function and the [transition rules](notes/2026-11-7-operational-semantics/) agree.

# Compute a Reply and a State

The model uses `Command.push` and `Command.pop`, with four possible reply forms. A function
returns a pair consisting of the reply and the next list:

```leanInit executable
```

```lean executable
open Course.Queue

def reference (capacity : Nat) (queue : List Word) : Command → Reply × List Word
  | .push value =>
      if queue.length < capacity then (.ok, queue ++ [value]) else (.full, queue)
  | .pop =>
      match queue with
      | [] => (.empty, [])
      | value :: rest => (.value value, rest)

example : reference 2 [7, 9] (.push 11) = (.full, [7, 9]) := by decide
example : reference 2 [7, 9] .pop = (.value 7, [9]) := by decide
example : reference 2 [] .pop = (.empty, []) := by decide
```

This function is total: it returns a result even for a list exceeding capacity. Our semantic
agreement theorem will require a valid input. For an oversized list, the function reports
`full`, whereas the semantics' full-push rule requires equality with capacity. We are making
no agreement claim for that malformed input.

The shared model calls the same function `run`. The definitions agree by computation:

```lean executable
example : reference = run := by rfl
```

Using lists keeps the computation close to the contract. Appending at the end requires
traversing the list, so this is a reference implementation rather than our intended low-level
queue representation.

# Prove Agreement in Both Directions

Soundness says that the computed reply and state satisfy the transition relation. Completeness
says that every permitted reply and state are the computed ones. The shared model combines
them in `step_iff_run`:

```lean executable
example (valid : Valid capacity queue) :
    Step capacity queue command reply next ↔
      reference capacity queue command = (reply, next) := by
  exact step_iff_run valid
```

For soundness, split on the command. Push splits again on available space; validity turns
failure of the strict inequality into equality with capacity. Pop splits on the list.
Each branch supplies the matching transition constructor.

For completeness, inspect a derivation of `Step`. Its constructor identifies the matching
branch of the function. The room or full premise justifies the conditional, while the pop
constructors determine the list pattern.

These arguments are small because both descriptions express the same design directly.
Keeping the relation and function separately stated still matters: their agreement is an
obligation we can inspect, rather than something hidden in the definition of correctness.

# From Agreement to Other Results

A valid state and command have a transition: run the function and apply soundness.
Transitions are deterministic: completeness makes any two results equal to the same function
result. Preservation then ensures that the next call again meets the validity premise.

A client can iterate this reference model over a list of commands. Record each reply and
thread the resulting queue into the next call. Differential tests can run the same commands
against another implementation and compare both replies and logical contents after each call.

A passing test trace checks particular calls. The agreement theorem quantifies over every
valid input and command. Conversely, the theorem does not show that our intended contract
is adequate: a perfectly implemented wrong specification remains wrong for its users.

# Exercise

Implement a trace runner, starting from empty. Check the six-command capacity-two example
from the specification post. Then prove that its final state is valid using soundness and
preservation, with induction over the command list.

Next: [Representation Invariants](notes/2026-11-7-representation-invariants/) replaces the
list with a circular buffer.
