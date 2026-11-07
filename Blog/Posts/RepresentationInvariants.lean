import VersoBlog
import Blog.Examples.CircularBufferChecks

open Verso Genre Blog

#doc (Post) "Representation Invariants" =>

%%%
authors := ["David Van Horn"]
date := {year := 2026, month := 11, day := 7}
%%%

The list reference model makes FIFO behavior easy to describe. A circular buffer makes
storage bounded and avoids shifting elements after every pop. To connect them, we need a
precise account of what a buffer state means.

The implementation and proofs in this post are checked by Lean. They live in
`Blog/Examples/CircularBuffer.lean`; concrete regression examples live in
`Blog/Examples/CircularBufferChecks.lean`. To try the examples in this website's Lean project,
import `Blog.Examples.CircularBufferChecks` at the top of your file.

# Storage and Logical Contents

`Buffer.State` contains an array `slots`, a head index `head`, and a count `count`.
Capacity is fixed by the client and equals the array size; it is not duplicated in a runtime
field. `Buffer.Valid capacity buffer` requires:

- `capacity > 0` and `buffer.slots.size = capacity`.
- `buffer.head < capacity`.
- `buffer.count <= capacity`.

Indices and counts are mathematical natural numbers. Slots contain unsigned 64-bit words,
matching the abstract element type. Machine-sized metadata will require additional bounds.

`Buffer.view` reads the occupied slots in logical order. For logical position `i` with
`0 <= i < count`, read physical slot `(head + i) mod slots.size`. The definition maps these
reads over `List.range count`. Its length is exactly `count`.

Here is a wrapped buffer whose fourth physical slot precedes its first in logical order:

```leanInit representation
```

```lean representation
open Course.Queue

def sample : Buffer.State := ⟨#[9, 99, 7, 8], 2, 3⟩

example : Buffer.view sample = [7, 8, 9] := by decide

example : Buffer.Rep 4 sample [7, 8, 9] := by
  unfold Buffer.Rep Buffer.Valid Buffer.view Buffer.contents sample
  decide
```

The notation `#[...]` constructs an array. Its unused slot contains 99; that value contributes
nothing to the logical queue. `Buffer.Rep capacity buffer queue` combines the concrete
invariant with the equation `Buffer.view buffer = queue`.

# The Abstraction Function Forgets Details

Many concrete states represent the same queue. An empty queue may have any in-range head
and arbitrary old payload values. Popping need not clear the removed slot because the new
view no longer includes it. A separate requirement to erase secrets would change this contract.

Initialization fills the array with zeroes and sets head and count to zero. It represents
the empty queue for every positive capacity:

```lean representation
example (positive : 0 < capacity) : Buffer.Rep capacity (Buffer.empty capacity) [] := by
  exact Buffer.empty_rep positive
```

Representation also implies abstract validity: the view has length `count`, and the invariant
bounds that count by capacity. `Buffer.rep_valid` packages this connection.

# Implement Push and Pop

The following definitions expose the code used by the library. The reflexivity proofs check
that the displayed functions are definitionally equal to `Buffer.push` and `Buffer.pop`:

```lean representation
def push (buffer : Buffer.State) (value : Word) : Reply × Buffer.State :=
  if buffer.count < buffer.slots.size then
    (.ok, { buffer with
      slots := buffer.slots.setIfInBounds ((buffer.head + buffer.count) % buffer.slots.size) value
      count := buffer.count + 1 })
  else (.full, buffer)

def pop (buffer : Buffer.State) : Reply × Buffer.State :=
  if buffer.count = 0 then (.empty, buffer)
  else
    (.value (buffer.slots[buffer.head]?.getD 0),
      { buffer with head := (buffer.head + 1) % buffer.slots.size, count := buffer.count - 1 })

example : push = Buffer.push := by rfl
example : pop = Buffer.pop := by rfl
```

`setIfInBounds` updates an existing array slot without resizing the array. Optional lookup
followed by `getD 0` makes reads total even for malformed states. The proofs establish that
all reads and writes used by valid operations are in bounds, so a default value cannot
substitute for a missing occupied slot. There is no correctness claim for malformed states.

A successful push writes the logical tail and increments the count. Pop reads the head,
advances it modulo capacity, and decrements the count. Full push and empty pop preserve
the entire state. Checking the count distinguishes full and empty even when their head and
tail positions coincide; all array slots are usable, including at capacity one.

In our example, pushing 10 fills physical slot one; popping then advances the head to three:

```lean representation
example : Buffer.push sample 10 = (.ok, ⟨#[9, 10, 7, 8], 2, 4⟩) := by decide

example : Buffer.pop (Buffer.push sample 10).2 =
    (.value 7, ⟨#[9, 10, 7, 8], 3, 3⟩) := by decide
```

# Prove the Representation Lemmas

Successful push must not overwrite any occupied slot. `Buffer.slot_injective` proves that
logical positions less than capacity have distinct modular indices. Because `count < capacity`,
the write at logical position `count` is distinct from all positions below it.
`Buffer.contents_push` then proves that the updated view is the old view followed by the
new value.

For pop, `Buffer.contents_pop` expresses a nonempty view as the head value followed by the
contents starting at the advanced head. The modular identity connecting the two sets of
indices establishes that the remaining view is exactly the old tail.

`Buffer.run_valid` proves invariant preservation for both commands:

```lean representation
example (valid : Buffer.Valid capacity buffer) (command : Command) :
    Buffer.Valid capacity (Buffer.run buffer command).2 := by
  exact Buffer.run_valid valid command
```

These results separate two questions. Bounds establish valid array access; view lemmas
establish what the accessed storage means. Both are needed for correctness.

# Exercise

Work through capacity one, a full queue, and a pop followed by a push that wraps around.
For each case, write the physical slots, head, count, and view. Explain why `head = 0` cannot
serve as an invariant for every reachable buffer. Then locate the corresponding cases in
the checked implementation and proofs.

Next: [Refinement and Simulation](notes/2026-11-7-refinement-and-simulation/) connects these
results to the abstract transition rules and complete client traces.
