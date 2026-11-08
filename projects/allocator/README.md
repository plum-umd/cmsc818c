# Project 1: A small allocator

Build a precise contract for a small memory allocator and use an agent to help
construct proofs of that contract. This project is about allocation invariants,
freshness, failure, and preservation of unrelated state. It does not require the
PL/OS repository, Verso, Mathlib, or a RISC instruction interpreter.

## What is supplied

- `Allocator/Machine.lean`: 64-bit words, byte memory, and half-open blocks.
- `Allocator/Basic.lean`: an executable bump allocator, an independent step
  relation, a checked initialization lemma, and a checked payload-frame lemma.
- `Allocator/Exercises.lean`: precise propositions for students to prove.
- `Checks.lean`: regression checks for representative executions and boundaries.

The universal exercise propositions are **not yet proved**. Defining a proposition
is not proving it, and a successful starter build does not complete the project.
There are no proof placeholders or assumed solutions in the supplied library.

## Build and explore

From this repository's root:

```sh
cd projects/allocator
lake build
```

Open this directory as a project in your Lean editor. It has its own pinned
toolchain, Lean 4.27.0, matching the inspected PL/OS RISC model. The website uses
a separate toolchain. No website build is needed here.

`lake build` checks both the library and every `#guard` in `Checks.lean`.
The examples check invalid sizes, exhaustion, exact fits, sequential allocations,
payload preservation, invalid initial memory, and the top of the address space.
They supplement the proof work; they do not replace it.

## The contract

The caller supplies a finite byte array at an absolute byte address. `init`
rejects a misaligned base or backing interval extending beyond `2^64`. An empty
backing array is allowed. A valid heap has an eight-byte-aligned cursor between
the base and the end of its backing storage.

`allocate heap request` returns a reply **and** the next heap. Requests are
64-bit unsigned words interpreted as byte counts. The cases, in priority order:

1. A zero request returns `zeroSize`.
2. A size not divisible by eight returns `unalignedSize`.
3. If the whole request fits, return the block starting at the current cursor
   and advance the cursor by exactly the requested size.
4. Otherwise return `outOfMemory`.

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

## Work in stages

1. **Read the model.** Explain what each invariant conjunct rules out. Predict
   the checks before executing them. Explain why returning the empty block for
   every request would fail the success contract.
2. **Connect function and relation.** Prove `Exercises.Soundness` and
   `Exercises.Completeness`. Derive determinism of `Step`. The relation fixes
   error priority as well as success behavior.
3. **Establish safety.** Prove `Exercises.Preservation`,
   `Exercises.FailureAtomicity`, and `Exercises.SuccessContract`. In particular,
   establish alignment, positive size, exact pointer conversion, containment,
   and cursor advancement. Do not assume these conclusions as hypotheses.
4. **Compose calls.** Prove `Exercises.Freshness` and
   `Exercises.ConsecutiveDisjointness`. Generalize to a trace with a history of
   returned blocks: all successful allocations are pairwise disjoint, errors
   leave the history unchanged, and old blocks stay within the backing interval.
5. **Review the frame.** Read the supplied `allocate_memory` proof and explain
   why it implies preservation of previously allocated contents. State what
   additional proof would be needed for an allocator that clears new blocks.
6. **Replace the implementation.** Implement a second version that compares the
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

```sh
lake env lean Audit.lean
```

Add the names of your own theorems to that audit. Do not add axioms or use
`sorry`/`admit` to discharge project obligations. If a proof seems to require
changing a contract, first explain the proposed change and obtain instructor
agreement. Retain tests for boundary cases even after the universal proofs pass.

## Deliberate limits and extensions

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

## Consistency with PL/OS

The design was checked against `Plos/RiscV/Model.lean` and its README in the
`../plos-risc` checkout at revision
`353b00002fe6fdb6a21d3c494945f616162f261a`. The build does not import PL/OS or depend
on a sibling checkout.

| Convention | PL/OS RISC model | This project |
| --- | --- | --- |
| Machine words and pointers | `BitVec 64` | Same |
| Backing storage | `base : Nat`, `bytes : Array UInt8` | Same field types |
| Address ranges | Half-open, whole access within backing and `2^64` | Same interval convention for blocks |
| Double-word access | Eight-byte alignment | Eight-byte-aligned allocations and sizes |
| Arithmetic | Register addition wraps; checked ranges must not wrap | Mathematical bounds checks before pointer conversion |
| Failure | Explicit fault, no partially updated state | Explicit allocation error, unchanged heap |
| Endianness | Little-endian multi-byte accesses | No multi-byte accesses yet; a later extension should use little endian |
| Protection | Host-owned regions and access permissions | Omitted; assume exclusive control of the backing interval |
| Execution | Registers, PC, instructions, traps, fuel | Omitted; direct sequential Lean function calls |

An allocation ending at `2^64` is permitted as an interval, but its end is not a
representable pointer. The sentinel therefore belongs to allocator metadata,
not a guest register. A later machine implementation must choose and prove a
representation for exhaustion, or restrict its heap bounds explicitly.

This correspondence is documented, not mechanically proved. Proving this
allocator correct will not by itself prove a separately written RISC allocator
correct. Connecting those implementations is a subsequent refinement exercise.
