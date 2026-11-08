import VersoBlog
import Blog.Examples.Queue

open Verso Genre Blog

#doc (Post) "Operational Semantics" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

The [queue specification](notes/2026-11-7-what-makes-a-good-specification/) describes what
clients should observe. An operational semantics gives that description a mathematical form:
a relation between an initial state, an operation, its reply, and a final state.

# States and Transitions

Fix a capacity `C`. The abstract state `q` is a list of unsigned 64-bit words. A valid state
satisfies `length(q) <= C`. We write `Step C q command reply next` for one complete interface
operation. This is a relation: a proposition that may hold for particular arguments.

There are four rules:

- If `length(q) < C`, pushing `x` returns `ok` and leaves `q ++ [x]`.
- If `length(q) = C`, pushing `x` returns `full` and leaves `q`.
- Popping `x :: rest` returns `value(x)` and leaves `rest`.
- Popping `[]` returns `empty` and leaves `[]`.

The condition above each rule is its premise; the permitted transition is its conclusion.
There are no other constructors for a step. A successful push into a full queue therefore
has no derivation.

# Rules as Lean Constructors

The shared model in `projects/queue/Queue/Model.lean` represents commands and replies with inductive
types and the rules with an inductive proposition. Its constructors are `Step.push`,
`Step.full`, `Step.pop`, and `Step.empty`. For example:

```leanInit semantics
```

```lean semantics
open Course.Queue

example : Step 2 [] (.push 7) .ok [7] :=
  Step.push (by decide)

example : Step 2 [7, 9] (.push 11) .full [7, 9] :=
  Step.full (by decide)

example : Step 2 [7, 9] .pop (.value 7) [9] :=
  Step.pop
```

The push constructor needs evidence that space is available. Here `by decide` checks a
concrete arithmetic proposition. Pop needs no arithmetic premise: the nonempty list pattern
already identifies the returned value and remaining contents.

Notice that `Step` alone does not require the initial queue to satisfy the capacity bound.
For example, its pop rule applies to any nonempty list. We will state theorems with validity
premises when needed rather than assume that the type of a transition enforces every invariant.

# Executions and Observations

An execution is a chain of transitions in which each final state becomes the next initial
state. Starting empty at capacity two, push 7, push 9, and pop produces states `[]`, `[7]`,
`[7, 9]`, and `[9]`, with replies `ok`, `ok`, and `value(7)`.

The command/reply pairs label the transitions. Their sequence is a trace describing an
interaction with a client. State captures what remains available for future operations;
labels capture what happened at the interface. Both matter when comparing implementations.

Our step represents one whole queue operation. Later, an instruction semantics will describe
smaller steps, often one instruction at a time. Neither granularity is inherently the right
one for every question. Refinement will connect a finite machine execution to one queue step.

# Determinism and Defined Behavior

For a fixed valid state and command, the rules give a unique reply and next state. Push's
room and full conditions cannot both hold; a list cannot be empty and nonempty at once.
Every valid input also has a transition. These are separate facts: uniqueness does not imply
existence. A relation with no transitions is deterministic but useless as a total queue API.

This queue semantics is deterministic. An OS semantics may deliberately permit several
possible schedules. In that case, correctness means choosing permitted behavior; equality
with one particular schedule would be too restrictive.

# Exercise

Derive the complete capacity-two trace from the previous post. Identify the rule used at
each step. Then remove the `Step.empty` rule: which property fails, existence or uniqueness?

Next: [Invariants and Induction](notes/2026-11-7-invariants-and-induction/) establishes that
these transitions preserve valid states.
