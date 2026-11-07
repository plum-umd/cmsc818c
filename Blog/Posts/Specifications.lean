import VersoBlog
import Blog.Examples.Queue

open Verso Genre Blog

#doc (Post) "What Makes a Good Specification?" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

A proof answers a precise question. Before asking whether a queue implementation is correct,
we need to decide which question to ask. We will use the bounded queue from the
[warm-up](notes/2026-11-7-warmup-a-verified-queue-from-semantics-to-risc/) to turn an informal
requirement into a contract we can implement and check.

# Start with Observable Behavior

A first-in, first-out queue stores elements until a client removes them. Fix a positive
capacity `C`. Elements are unsigned 64-bit words, and duplicates are permitted. Calls are
sequential: one operation finishes before the next begins.

The interface has two commands. `push(x)` returns `ok` and appends `x` when there is room.
When the queue is full, it returns `full` and preserves the contents. `pop` returns
`value(x)` and removes the oldest element; on an empty queue it returns `empty` and
preserves the contents. A separate status distinguishes an empty queue from a stored zero.

With capacity two, consider pushing 7, pushing 9, pushing 11, and popping three times.
The replies must be `ok`, `ok`, `full`, `value(7)`, `value(9)`, and `empty`.
The rejected push must leave both existing elements intact.

# Try to Satisfy the Wrong Specification

Suppose we require only that a successful pop returns an element previously pushed.
A stack satisfies this requirement: it can return the newest element first. A broken
implementation that repeatedly returns the same old element might satisfy it too.
We have omitted order and removal.

Suppose we add only a bound on the number of stored elements. An implementation that
always reports `full` and never stores anything remains within the bound. We must require
success when there is space. Similarly, requiring a correct value _if_ pop succeeds permits
an implementation that always reports `empty`.

Even preserving the multiset of elements is insufficient to establish FIFO order.
The queue's abstract state should therefore be a sequence, with operations specifying both
the reply and the next sequence. This makes loss, duplication, and reordering visible.

A useful review technique is to propose a deliberately bad implementation and ask whether
the specification rules it out. If it does not, another proof will not repair the omission.

# Separate Requirements from Representation

The behavioral contract does not say whether the queue uses a list, a circular array, or
linked records. Clients need a predictable interface; implementations need room to choose
representations. Later, a representation relation will connect storage to the abstract
sequence.

The abstract state invariant is `length(q) <= C`. For a valid queue, every command must
have a specified result. Calls on full or empty queues are ordinary interface cases.
A corrupted length field in a machine implementation is a different matter: initially,
we will exclude malformed representations using a precondition. A defensive interface
could instead specify validation and an additional error result.

Our contract also needs an execution boundary. For this exercise, the caller supplies
valid, exclusively owned storage, and operations run without concurrent interference.
Memory safety, termination, and preservation of unrelated state will become explicit
obligations when we introduce machine execution. Functional input/output behavior alone
does not imply those properties.

# Preconditions Deserve Scrutiny

A precondition is a promise the caller must establish. Requiring valid storage and sufficient
address space can be appropriate. Requiring the queue to contain fewer than `C - 1` elements
would silently exclude a legitimate successful push into the last free slot.

An impossible precondition makes any implication true. Less obvious restrictions can also
remove precisely the cases that expose a bug. Review assumptions against real client calls,
and check that initialization can establish them and each operation preserves them.

# Exercise

For each proposed contract, give a bad implementation or explain why none exists:

1. Pop returns the oldest element, but the next state is unspecified.
2. A full push preserves the state, but its reply is unspecified.
3. Every operation is correct provided the circular buffer never wraps around.

Write down the missing requirement in each case. Ask an agent to find counterexamples to
your revised contract, then assess its examples yourself.

Next: [Operational Semantics](notes/2026-11-7-operational-semantics/) turns the contract into
explicit transition rules.
