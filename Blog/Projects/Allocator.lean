import VersoBlog
import Allocator

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "."

#doc (Page) "Project 1: A Small Allocator" =>

Build a precise contract for a small memory allocator and use an agent to help
construct proofs of that contract. This project is about allocation invariants,
freshness, failure, and preservation of unrelated state.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/allocator)
contains the files for this project.

# What is supplied

- `Allocator/Machine.lean`: 64-bit words, byte memory, and half-open blocks.
- `Allocator/Basic.lean`: an executable bump allocator, an independent step
  relation, a checked initialization lemma, and a checked payload-frame lemma.
- `Allocator/Exercises.lean`: precise propositions for students to prove.
- `Checks.lean`: regression checks for representative executions and boundaries.

The universal exercise propositions are *not yet proved*. Defining a proposition
is not proving it, and a successful starter build does not complete the project.
There are no proof placeholders or assumed solutions in the supplied library.

# Build and explore

From this repository's root:

```
cd projects/allocator
lake build
```

Open this directory as a project in your Lean editor. It has its own pinned
toolchain, Lean 4.27.0.

`lake build` checks both the library and every `#guard` in `Checks.lean`.
The examples check invalid sizes, exhaustion, exact fits, sequential allocations,
payload preservation, invalid initial memory, and the top of the address space.
They supplement the proof work; they do not replace it.

# Machine.lean: Words, Blocks, and Backing Memory

Start with `Allocator/Machine.lean`. This module defines the vocabulary used by the allocator.
It describes addresses and storage; it does not execute instructions or allocate blocks.
All its definitions live in the namespace `Course.Allocator`.

## Words and Byte Counts

```anchor machineWords (module := Allocator.Machine)
abbrev Word := BitVec 64

def addressLimit : Nat := 2 ^ 64

def wordBytes : Nat := 8
```

`Word` is a 64-bit bitvector. A pointer or request represented by a `Word` has an unsigned
value between zero and `2^64 - 1`, obtained with `.toNat`. The address-space limit itself
is a `Nat`: it is one past the greatest representable pointer. `wordBytes` is eight because
one 64-bit word occupies eight bytes. Addresses and allocation sizes count *bytes*, not words.

## Blocks Are Intervals

```anchor blocks (module := Allocator.Machine)
structure Block where
  start : Word
  size : Nat
  deriving DecidableEq, Repr

def Block.finish (block : Block) : Nat := block.start.toNat + block.size

def Block.Contains (block : Block) (address : Nat) : Prop :=
  block.start.toNat ≤ address ∧ address < block.finish

def Block.Disjoint (left right : Block) : Prop :=
  left.finish ≤ right.start.toNat ∨ right.finish ≤ left.start.toNat
```

A block describes the half-open interval `[start, finish)`. A block starting at `0x1000`
with size eight contains addresses `0x1000` through `0x1007`; its end is `0x1008`.
The end is computed using natural-number arithmetic, so it cannot silently wrap.

`Contains` says that a byte address lies in that interval. `Disjoint` says that one block
ends before or exactly where the other starts. Adjacent blocks are therefore disjoint.
Neither predicate checks that a block is backed by memory or fits the address space:
those requirements appear in the allocator's contracts.

`deriving DecidableEq, Repr` asks Lean to supply equality comparison and a representation
for displaying values. It does not establish any of the project's correctness properties.

## Memory Holds the Actual Bytes

```anchor memory (module := Allocator.Machine)
structure Memory where
  base : Nat
  bytes : Array UInt8
  deriving DecidableEq, Repr

def Memory.finish (memory : Memory) : Nat := memory.base + memory.bytes.size
```

`Memory` is the backing storage. Array index zero corresponds to address `base`; index `i`
corresponds to address `base + i`. Its interval is `[base, base + bytes.size)`.
`UInt8` represents one byte, while `Array.size` counts how many bytes exist.

The distinction between `Block` and `Memory` matters: returning a block does not create
new backing bytes. The allocator must carve every returned block out of the supplied memory.

# Basic.lean: State and the Allocation Contract

`Allocator/Basic.lean` imports the memory vocabulary, then adds allocator state, initialization,
replies, the executable allocation function, and a relation specifying permitted steps.

## The Heap Records the Allocation Frontier

```anchor heap (module := Allocator.Basic)
structure Heap where
  memory : Memory
  next : Nat
  deriving DecidableEq, Repr
```

`Heap.memory` is the backing storage, and `Heap.next` is the next free byte address.
This is a bump allocator: successful allocations advance that frontier, without searching
for gaps or maintaining a free list. Its history is implicit. Bytes before `next` have been
consumed by earlier allocations; bytes from `next` to the end remain available.

## Validity and Initialization

```leanInit allocator
```

```lean allocator
open Course.Allocator
```

The memory model stores bytes at an absolute base address. Blocks describe half-open intervals:
the start belongs to the block, and the end does not. The cursor identifies the next free byte.
The starter defines the heap invariant as follows:

```anchor heapValid (module := Allocator.Basic)
def Heap.Valid (heap : Heap) : Prop :=
  heap.memory.base % wordBytes = 0 ∧
  heap.next % wordBytes = 0 ∧
  heap.memory.base ≤ heap.next ∧
  heap.next ≤ heap.memory.finish ∧
  heap.memory.finish ≤ addressLimit
```

Read the conjunction from top to bottom: base and cursor are aligned, the cursor is not
before the backing storage, the cursor is not past its end, and the backing storage itself
does not cross the address-space limit. Validity is a proposition about a `Heap`, rather
than an extra field of the structure. Constructing a `Heap` value does not automatically
prove that it is valid.

```anchor initialize (module := Allocator.Basic)
def init (memory : Memory) : Option Heap :=
  if memory.base % wordBytes = 0 ∧ memory.finish ≤ addressLimit then
    some ⟨memory, memory.base⟩
  else none
```

The caller supplies a finite byte array at an absolute byte address. `init`
rejects a misaligned base or backing interval extending beyond `2^64`. An empty
backing array is allowed. A valid heap has an eight-byte-aligned cursor between
the base and the end of its backing storage.

`some ⟨memory, memory.base⟩` constructs a heap with its cursor at the base; `none` reports
that initialization rejected the supplied memory. The provided theorem `init_valid` states
that every heap returned by `init` satisfies `Heap.Valid`.

## Replies Make Failure Explicit

```anchor replies (module := Allocator.Basic)
inductive Error where
  | zeroSize
  | unalignedSize
  | outOfMemory
  deriving DecidableEq, Repr

inductive Reply where
  | allocated (block : Block)
  | error (reason : Error)
  deriving DecidableEq, Repr
```

An inductive type describes alternatives. A `Reply` either contains an allocated `Block`
or an `Error` explaining the failure. Clients distinguish these cases by pattern matching.
This keeps an error separate from every successful address, including address zero.

## Executing an Allocation

`allocate heap request` returns a reply *and* the next heap. Requests are
64-bit unsigned words interpreted as byte counts. The cases, in priority order:

1. A zero request returns `zeroSize`.
2. A size not divisible by eight returns `unalignedSize`.
3. If the whole request fits, return the block starting at the current cursor
   and advance the cursor by exactly the requested size.
4. Otherwise return `outOfMemory`.

Here is the allocation function from the starter:

```anchor allocate (module := Allocator.Basic)
def allocate (heap : Heap) (request : Word) : Reply × Heap :=
  let size := request.toNat
  if size = 0 then (.error .zeroSize, heap)
  else if size % wordBytes ≠ 0 then (.error .unalignedSize, heap)
  else if heap.next + size ≤ heap.memory.finish then
    (.allocated ⟨BitVec.ofNat 64 heap.next, size⟩, { heap with next := heap.next + size })
  else (.error .outOfMemory, heap)
```

The result type `Reply × Heap` is a pair: `.1` selects the reply and `.2` selects the
next state. `{ heap with next := ... }` constructs a state with an updated cursor and
the same memory. Returning `heap` on an error leaves the entire state unchanged.

Every error preserves the whole input heap. Every successful allocation preserves
all backing bytes. Allocation grants a logical block; it does not initialize its
contents or modify hardware permissions. Address zero is a legitimate address,
so failure has a separate constructor, not a null-pointer encoding.

The API has a valid-heap precondition for the safety results. Heap fields remain
visible so students can state and reason about invalid representations; arbitrary
hand-constructed heaps are not guaranteed to be safe. `init_valid` establishes
the invariant at the entry point, and preservation must establish it after calls.

The heap cursor is a `Nat`, rather than a machine word. It can equal `2^64` as
a one-past-the-end sentinel. A successful positive request must start strictly
below that limit: proving that fact is necessary before treating `BitVec.ofNat`
as an exact pointer conversion. Bounds arithmetic uses `Nat` to check for
overflow instead of allowing machine addition to wrap silently.

## Describing a Step Independently

The function computes a result. `Step heap request reply next` instead states that a
particular reply and next state are permitted for a request:

```anchor allocationStep (module := Allocator.Basic)
inductive Step (heap : Heap) (request : Word) : Reply → Heap → Prop where
  | zero (empty : request.toNat = 0) : Step heap request (.error .zeroSize) heap
  | unaligned (positive : request.toNat ≠ 0) (bad : request.toNat % wordBytes ≠ 0) :
      Step heap request (.error .unalignedSize) heap
  | full (positive : request.toNat ≠ 0) (aligned : request.toNat % wordBytes = 0)
      (full : heap.memory.finish < heap.next + request.toNat) :
      Step heap request (.error .outOfMemory) heap
  | success (positive : request.toNat ≠ 0) (aligned : request.toNat % wordBytes = 0)
      (room : heap.next + request.toNat ≤ heap.memory.finish) :
      Step heap request (.allocated ⟨BitVec.ofNat 64 heap.next, request.toNat⟩)
        { heap with next := heap.next + request.toNat }
```

Each constructor is a rule. Its named arguments are the premises needed to justify the
conclusion after the colon. For example, `success` requires a nonzero, aligned request that
fits in the remaining storage. The rule then fixes the returned block and the updated cursor.
The error rules also state which conditions must hold, preserving the function's error priority.

The relation contains no call to `allocate`. Proving soundness connects the function's
computed result to these rules; proving completeness establishes that every permitted result
is the one the function computes. Separately, invariant preservation explains why a valid
input leads to a valid next heap. These are different obligations.

The module ends with two supplied proofs: `init_valid` establishes validity after initialization,
and `allocate_memory` establishes that allocation preserves the backing memory. The latter
is used below. The remaining project obligations are stated in `Allocator/Exercises.lean`.

# Try Some Calls

The following examples are checked as part of this page. This heap has 24 bytes, initially
filled with `0xA5`. One allocation consumes the first eight bytes; the next consumes the
remaining sixteen. A further request fails and preserves the full state:

```lean allocator
def initialHeap : Heap := ⟨⟨0x1000, Array.replicate 24 0xA5⟩, 0x1000⟩
def afterFirst : Heap := (allocate initialHeap 8).2
def afterSecond : Heap := (allocate afterFirst 16).2

example : initialHeap.Valid := by
  unfold Heap.Valid
  decide
example : allocate initialHeap 8 =
    (.allocated ⟨0x1000, 8⟩, { initialHeap with next := 0x1008 }) := by decide
example : (allocate afterFirst 16).1 = .allocated ⟨0x1008, 16⟩ := by decide
example : allocate afterSecond 8 = (.error .outOfMemory, afterSecond) := by decide
example : allocate initialHeap 7 = (.error .unalignedSize, initialHeap) := by decide
```

At the upper boundary, the last eight bytes may be allocated, but the next cursor must be
`2^64`, not zero. Further allocation fails:

```lean allocator
def topHeap : Heap :=
  ⟨⟨addressLimit - 8, Array.replicate 8 0⟩, addressLimit - 8⟩

example : (allocate topHeap 8).2.next = addressLimit := by decide
example : allocate (allocate topHeap 8).2 8 =
    (.error .outOfMemory, (allocate topHeap 8).2) := by decide
```

These are particular executions. The supplied frame theorem covers *every* heap and request:

```lean allocator
example (heap : Heap) (request : Word) :
    (allocate heap request).2.memory = heap.memory := by
  exact allocate_memory heap request
```

Inspecting the proof states can help distinguish what computation establishes in the concrete
examples from what the frame theorem establishes universally.

# Work in stages

The project states proof goals as propositions. For example, invariant preservation is exactly:

```anchor preservation (module := Allocator.Exercises)
def Preservation : Prop :=
  ∀ (heap : Heap) (request : Word), heap.Valid → (allocate heap request).2.Valid
```

This definition states the obligation; it does not prove preservation. Your task is to
construct a proof of this proposition and the other obligations below.

1. *Read the model.* Explain what each invariant conjunct rules out. Predict
   the checks before executing them. Explain why returning the empty block for
   every request would fail the success contract.
2. *Connect function and relation.* Prove `Exercises.Soundness` and
   `Exercises.Completeness`. Derive determinism of `Step`. The relation fixes
   error priority as well as success behavior.
3. *Establish safety.* Prove `Exercises.Preservation`,
   `Exercises.FailureAtomicity`, and `Exercises.SuccessContract`. In particular,
   establish alignment, positive size, exact pointer conversion, containment,
   and cursor advancement. Do not assume these conclusions as hypotheses.
4. *Compose calls.* Prove `Exercises.Freshness` and
   `Exercises.ConsecutiveDisjointness`. Generalize to a trace with a history of
   returned blocks: all successful allocations are pairwise disjoint, errors
   leave the history unchanged, and old blocks stay within the backing interval.
5. *Review the frame.* Read the supplied `allocate_memory` proof and explain
   why it implies preservation of previously allocated contents. State what
   additional proof would be needed for an allocator that clears new blocks.
6. *Replace the implementation.* Implement a second version that compares the
   request against remaining capacity, `memory.finish - next`, before advancing
   the cursor. Prove agreement with the reference on valid heaps and transfer
   the contracts. Explain why the validity precondition matters when subtraction
   on natural numbers truncates at zero.

Create `Allocator/Solution.lean`, import `Allocator.Exercises`, and write proofs
such as `theorem preservation : Exercises.Preservation := by ...`. Import your
solution from `Checks.lean` so the ordinary build checks it. Keep the supplied
definitions and proposition statements fixed. Submit the implementation and
proofs together with a short account of the specification, assumptions, trusted
boundary, and your use of an agent.

Start by asking the agent to explain a theorem and propose a proof plan. Then
have it attempt one lemma at a time, inspect Lean's feedback, and explain the
finished argument. Audit transitive assumptions; removing visible placeholders
alone does not establish that a proof is complete. The starter's
`Audit.lean` demonstrates `#print axioms` for the two supplied theorems:

```
lake env lean Audit.lean
```

Add the names of your own theorems to that audit. Do not add axioms or use
`sorry`/`admit` to discharge project obligations. If a proof seems to require
changing a contract, first explain the proposed change and obtain instructor
agreement. Retain tests for boundary cases even after the universal proofs pass.

# Deliberate limits and extensions

This first allocator only advances a cursor. There is no deallocation, reuse,
rounding of request sizes, concurrency, or persistence. Ownership is represented
by non-overlapping returned intervals; it is not dynamically enforced on arbitrary
memory accesses. Fresh storage is not necessarily zeroed.

Possible later tasks are to accept arbitrary sizes with checked alignment
rounding; add byte operations with a frame theorem; introduce a free list and
prove reuse safety; or lower a routine to a small instruction set. Those are
extensions, not prerequisites for completing the initial project. Deallocation
also raises a new problem: disjointness of live blocks does not alone prevent a
client from using a stale reference.
