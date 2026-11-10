import VersoBlog

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "projects/risc-handles"

#doc (Page) "Project 8: Persistent RISC Handle Tables" =>

Lookup reads a native table without changing it. This project adds a bounded append routine
and turns the two operations into a persistent component. You will write assembly that stores
a channel, prove exactly what it changes, and retain its resulting memory for subsequent calls.
The final milestone composes your append proof with the supplied lookup proof.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/risc-handles)
uses the same pinned PL/OS revision as Project 7. Lookup is supplied, so you do not need
your earlier solution. Assembly and the persistent adapter are implementation exercises;
their correctness properties are propositions to prove, not assumed theorems.

# Build and Explore

From the repository root:

```
cd projects/risc-handles
lake build
```

Open this directory as a Lean project. Lake downloads the pinned dependencies; no sibling
checkout is required. The project uses Lean 4.27.0.

- `RiscHandles/Spec.lean`: buffer representation, call inputs, and append contract.
- `RiscHandles/Program.lean`: the empty assembly body you will implement.
- `RiscHandles/Support.lean`: nonwrapping slot addresses and return-marker exclusion.
- `RiscHandles/Image.lean`: a supplied, verified loader for lookup, your append image, and data.
- `RiscHandles/Table.lean`: persistent representation, validity, and supplied initialization.
- `RiscHandles/Calls.lean`: supplied argument layouts and return markers.
- `RiscHandles/Native.lean`: execution wrappers and the persistent adapter placeholder.
- `RiscHandles/Exercises.lean`: the required proof obligations.
- `RiscHandles/Fixtures.lean`: executable routine and persistence checks.
- `Checks.lean` and `Audit.lean`: supplied checks and theorem-assumption reporting.

The upstream modules `Plos.RiscV.Lookup` and `Plos.RiscV.Memory` are supplied dependencies.
You may use their lookup correctness and generic load/store/frame theorems. Do not import
the completed upstream `Append`, `HandleImage`, `HandleTable`, or native handle adapter.
The audit rejects imports of the completed append or persistent native table.

# Two Milestones

First verify a standalone routine at arbitrary permitted code and buffer addresses. Its
specification includes successful append, refusal when full, exact byte effects, and a
register frame. Next implement an adapter that retains the memory and length returned
by execution, preserves a persistent invariant, and supports a later native lookup.

This component appends channel words to a bounded table. It does not allocate channels,
suppress duplicates, grow a full buffer, or implement the complete kernel grant policy.
Duplicates are valid entries here. Those policies can be added above this mechanism later.

# Specify the Buffer

```anchor buffer (module := RiscHandles.Spec)
/-- Existing readable cells, bounded capacity, and access to the next slot when there is room. -/
structure Buffer (memory : Memory) (mode : Mode) (address : Word)
    (channels : List Word) (capacity : Nat) : Prop where
  table : Lookup.Table memory mode address channels
  length_le : channels.length ≤ capacity
  fits : address.toNat + 8 * capacity ≤ 2^64
  readable : channels.length < capacity → ∃ previous,
    memory.load mode .read (address + BitVec.ofNat 64 (8 * channels.length)) .double = .ok previous
  writable : channels.length < capacity → ∃ after,
    memory.store64 mode (address + BitVec.ofNat 64 (8 * channels.length)) 0 = .ok after
```

The existing logical sequence is represented by successful eight-byte loads, as in Project 7.
The capacity bounds its length and prevents the entire reserved buffer from wrapping around
the address space. When there is room, the next cell must be both readable and writable.
Its previous value is unrestricted.

The writable condition uses a store of zero to witness access. The supplied
`Memory.store64_available` lemma transfers successful access to any word value. The new
channel may be zero, have its high bit set, or duplicate an existing entry.

When the buffer is full, no next slot is required. Access beyond the buffer must not be
part of the full path, even as a speculative load or store in this sequential model.

# Specify the Append Result

On entry, `a0` holds the buffer address, `a1` its length, `a2` its capacity, and `a3` the
channel to append. Return through `ra` with the resulting length in `a0` and a success flag
in `a1`. You may use `a4` as scratch. Preserve every other architectural register and the
privilege mode.

```anchor correct (module := RiscHandles.Spec)
/-- Append extends the table with one exact cell write, or refuses without changing memory. -/
def Correct (channels : List Word) (capacity : Nat) (address channel ret : Word)
    (before : State) (result : CallResult) : Prop :=
  result.stop = .returned ∧ result.state.pc = ret ∧ result.retired ≤ 16 ∧
    result.state.mode = before.mode ∧
    (∀ r : Register, r ≠ 10 → r ≠ 11 → r ≠ 14 →
      result.state.readReg r = before.readReg r) ∧
    if channels.length < capacity then
      result.state.readReg 10 = BitVec.ofNat 64 (channels.length + 1) ∧
      result.state.readReg 11 = 1 ∧
      Lookup.Table result.state.memory before.mode address (channels ++ [channel]) ∧
      Store64Effect before.memory result.state.memory
        (address + BitVec.ofNat 64 (8 * channels.length)) channel
    else
      result.state.readReg 10 = BitVec.ofNat 64 channels.length ∧
      result.state.readReg 11 = 0 ∧ result.state.memory = before.memory
```

On success, the logical sequence grows by one entry. `Store64Effect` specifies an exact
eight-byte write, preserves all other bytes, and retains the memory base, size, and regions.
It does not assert that each byte changes: storing the value already present is allowed.
On refusal, the length is unchanged, the flag is zero, and the entire memory is unchanged.

Both paths must return within 16 retired instructions. This is an upper bound, not a
requirement to reproduce the reference instruction sequence or its exact counts.

# Prove the Representation Lemma First

```anchor tableAppend (module := RiscHandles.Exercises)
/-- Derive the extended representation from the byte-level effect, independently of assembly. -/
def TableAppend : Prop :=
  ∀ (before after : Memory) (mode : Mode) (address channel : Word)
    (channels : List Word) (capacity : Nat),
    Buffer before mode address channels capacity → channels.length < capacity →
    Store64Effect before after (address + BitVec.ofNat 64 (8 * channels.length)) channel →
      Lookup.Table after mode address (channels ++ [channel])
```

Prove this property independently of your assembly. Split the represented entries into
old cells and the new final cell. For old entries, combine `Support.slot_address` with
`Store64Effect.load_preserved`. For the new cell, use `Store64Effect.load_self` and the
buffer's readable-slot witness. Account for the new sequence's length and address bound.

This separates a data-representation argument from the instruction trace. Later you will
only need to establish that execution produces the specified store effect.

# Implement and Verify the Assembly

```anchor program (module := RiscHandles.Program)
/-- Implement bounded append: a0 = buffer, a1 = length, a2 = capacity, a3 = channel.
Return a0 = new length, a1 = success. Only a0, a1, and a4 may change. -/
def program : List Assembler.Item := []

def code : Array InstructionWord :=
  (Assembler.assemble program).toOption.get (by decide +kernel)
```

Compare length and capacity as unsigned words before touching data. Compute the next cell
address, perform one eight-byte store when there is room, set the outputs, and return.
Keep the original length available until you have produced the new length. Inspect the
source-register order of `sd`: the model takes the address register before the value register.

Assembly must succeed by a checked proof. Prove the decoding facts needed by your trace;
do not replace an assembly error with an empty or default image.

```anchor inputs (module := RiscHandles.Spec)
structure Inputs (code : Array InstructionWord) (state : State) (base ret : Word)
    (channels : List Word) (capacity : Nat) : Prop where
  image : CodeAt state.memory state.mode base code
  location : ReturnAt base ret code
  buffer : Buffer state.memory state.mode (state.readReg 10) channels capacity
  separate : base.toNat + 4 * code.size ≤ (state.readReg 10).toNat ∨
    (state.readReg 10).toNat + 8 * capacity ≤ base.toNat
  entry : state.pc = base
  ra : state.readReg 1 = ret
  length : state.readReg 11 = BitVec.ofNat 64 channels.length
  capacity : state.readReg 12 = BitVec.ofNat 64 capacity
```

The code and reserved buffer occupy disjoint intervals. This assumption has an operational
purpose: after a store, the next instruction must be fetched from the updated memory.
Use `Memory.store64_effect` and `CodeAt.store64` to establish that the append code remains
installed. Do not continue using the pre-store code hypothesis as though memory were unchanged.

```anchor runCorrect (module := RiscHandles.Exercises)
def RunCorrect : Prop :=
  ∀ (state : State) (base ret : Word) (channels : List Word) (capacity fuel : Nat),
    Inputs code state base ret channels capacity → 16 ≤ fuel →
      Correct channels capacity (state.readReg 10) (state.readReg 13) ret state
        (resumeCall ret fuel state)
```

Prove the successful and full paths separately. Use `CodeAt.step` to justify encoded
instruction execution, `Support.not_return` to exclude premature completion, and `Returns.run`
to connect a terminating trace to all sufficient fuel allowances. Derive the successful
post-table with your `TableAppend` theorem. Include the output registers and register frame.

Also prove `Exercises.CallCorrect`, transferring your result through `callRoutine`.
Compare the frame to the prepared state: preparation itself sets argument registers,
the stack pointer, and `ra`.

# Retain a Native Table

The standalone proof describes one call. Persistence requires the result of that call to
be a valid input to the next one.

```anchor native (module := RiscHandles.Table)
/-- Bytes are authoritative; there is no stored logical list of channels. -/
structure Native where
  memory : Memory
  length : Nat
  capacity : Nat
  deriving DecidableEq

namespace Native

/-- Decode the logical view when needed for specifications, not for native lookup or append. -/
def words (table : Native) : List Word :=
  (List.range table.length).map fun i => BitVec.ofNat 64
    ((table.memory.load .user .read (256 + BitVec.ofNat 64 (8*i)) .double).toOption.getD 0)

/-- A persistent table retains both code images, its layout, and a represented logical sequence. -/
structure Valid (table : Native) : Prop where
  base : table.memory.base = 0
  size : table.memory.bytes.size = 256 + 8*table.capacity
  regions : table.memory.regions = Image.regions code table.capacity
  fits : 256 + 8*table.capacity ≤ 2^64
  length_le : table.length ≤ table.capacity
  codeBound : code.size ≤ 16
  lookupCode : Lookup.Code table.memory .user 0
  appendCode : CodeAt table.memory .user 64 code
  represented : ∃ channels : List Word, channels.length = table.length ∧
    Lookup.Table table.memory .user 256 channels
```

`Native` stores only the memory image and two metadata values. `Valid` is a separate
proposition; the represented list exists inside a proof, not as a runtime shadow table.
The supplied `words` function computes a logical view by decoding memory when a specification
needs it. Validity ensures those loads succeed, making its default value unreachable.
Do not implement append by decoding this view and constructing a fresh image.

The fixed layout is lookup at address 0, append at 64, and data at 256. The append return
marker is 192; lookup returns at 44. Only code is executable, and only data is writable.
This loader reserves space for at most 16 append instructions. Prove your assembled image
fits that limit; the standalone execution theorem still permits arbitrary valid locations.

```anchor init (module := RiscHandles.Table)
/-- Load a fresh image once; subsequent operations must retain their execution's memory. -/
def init (channels : List Word) (capacity : Nat) : Native :=
  ⟨Image.memory code channels capacity, channels.length, capacity⟩

theorem init_valid (channels : List Word) (capacity : Nat) (bound : code.size ≤ 16)
    (length : channels.length ≤ capacity) (fits : 256 + 8*capacity ≤ 2^64) :
    (init channels capacity).Valid :=
  ⟨Image.memory_base _ _ _, Image.memory_size _ _ _, (by unfold init Image.memory; rfl),
    fits, length, bound,
    Image.lookup_code _ _ _, Image.append_code _ bound _ _,
    channels, rfl, Image.table _ bound _ _ length fits⟩
```

The supplied initializer and its proofs establish that a fresh image satisfies the
representation. Use `Native.table`, `Native.words_length`, and `Native.slot_mapped` to
derive a `Buffer` for a valid table. These lemmas expose the data representation without
requiring you to redo byte serialization or memory-permission proofs.

# Execute Against the Retained Memory

```anchor calls (module := RiscHandles.Native)
def appendPrepared (table : Native) (channel : Word) : State :=
  ((table.appendCall channel).prepare { memory := table.memory }).toOption.get (by
    simp [appendCall, Call.prepare]; rfl)

def appendResult (table : Native) (channel : Word) : CallResult :=
  resumeCall 192 16 (table.appendPrepared channel)

def lookupPrepared (table : Native) (index : Nat) : State :=
  ((table.lookupCall index).prepare { memory := table.memory }).toOption.get (by
    simp [lookupCall, Lookup.invocation, Call.prepare]; rfl)

def lookupResult (table : Native) (index : Nat) : CallResult :=
  resumeCall 44 Lookup.allowance (table.lookupPrepared index)
```

These calls use `table.memory` directly. Lookup does not decode `words` or serialize a new
image before execution. Append likewise executes against the existing image; its result
contains the memory that the adapter must retain.

```anchor append (module := RiscHandles.Native)
/-- Replace this placeholder with an adapter that retains the native call's memory and length. -/
def append (table : Native) (_channel : Word) : Native := table
```

Replace this placeholder with the persistent adapter. Take its memory and resulting length
from `appendResult`; retain the capacity. A trapped or suspended execution is not a reason
to silently use a reference implementation. Your correctness theorem must establish that
valid calls return and that their results preserve validity.

```anchor nativeAppend (module := RiscHandles.Exercises)
/-- Preserve the persistent invariant while taking memory and length from encoded execution. -/
def NativeAppendCorrect : Prop :=
  ∀ (table : Native) (channel : Word), table.Valid →
    let result := table.appendResult channel
    let after := table.append channel
    result.stop = .returned ∧ after.Valid ∧
      after.memory = result.state.memory ∧
      after.length = (result.state.readReg 10).toNat ∧ after.capacity = table.capacity ∧
      if table.length < table.capacity then
        result.state.readReg 11 = 1 ∧ after.words = table.words ++ [channel] ∧
        Store64Effect table.memory after.memory
          (256 + BitVec.ofNat 64 (8 * table.length)) channel
      else result.state.readReg 11 = 0 ∧ after = table
```

To preserve `Valid`, use the store effect for base, size, and regions, and establish that
*both* code images survive. Use the extended represented sequence on success and the old
invariant on refusal. The next lookup needs its own installed code hypothesis, not merely
the fact that append could finish.

The explicit equalities with the call result rule out an adapter that computes the right
abstract list while discarding native execution. The full case requires the exact old
native value, not just an equivalent logical view.

# Compose Append and Lookup

```anchor nativeLookup (module := RiscHandles.Exercises)
def NativeLookupCorrect : Prop :=
  ∀ (table : Native) (index : Nat), table.Valid → index < 2^64 →
    Lookup.Correct table.words index (table.lookupPrepared index) (table.lookupResult index)

/-- The new cell can be read by the independently verified lookup without rebuilding an image. -/
def AppendThenLookup : Prop :=
  ∀ (table : Native) (channel : Word), table.Valid → table.length < table.capacity →
    let after := table.append channel
    let result := after.lookupResult table.length
    result.stop = .returned ∧ result.state.readReg 10 = channel ∧ result.state.readReg 11 = 1
```

Use the supplied lookup theorem to establish `NativeLookupCorrect`, then combine the
persistent append result and that lookup theorem to prove `AppendThenLookup`.
The appended index is the *old* length. Explain why it fits in a word and why it now
selects the new final cell. The high-level composition proof should not replay either
routine's instruction trace.

This lookup contract assumes a representable index. A host wrapper accepting arbitrary
natural-number handles must reject an oversized index before conversion, rather than
wrapping it to a different valid handle. Allocation validity is also a separate policy.

# Run Concrete Checks

After implementing the routine and adapter:

```
lake exe check-handles
```

The command intentionally fails for the starter. It checks successful and full calls,
zero capacity, duplicate and extreme channel values, relocation, exact memory effects,
register frames, and all suspension boundaries within the budget. It also exercises an
overfull call with no readable data mapping, using a misaligned data address: refusal
must not touch that address.

The persistence checks start with an existing table, append until full, and look up
every logical entry after every operation. They check that each adapter result uses the
actual execution's memory and length, and that another append leaves the full table unchanged.
Add a regression check motivated by a bug you encountered. Tests supplement the universal
proofs; a passing starter build checks the supplied loader and infrastructure only.

Suspension after a successful store is especially instructive. The saved memory may
already contain the new cell even though the routine has not returned. Resume from the
saved state with `resumeCall`; preparing a new call would restart the operation.

# Submit and Explain

Implement `program` and `Native.append`. Create `RiscHandles/Solution.lean` with proofs of
`TableAppend`, `RunCorrect`, `CallCorrect`, `NativeAppendCorrect`, `NativeLookupCorrect`,
and `AppendThenLookup`. Import your solution from `Checks.lean`, add assumption reports
for its theorems in `Audit.lean`, and run:

```
lake build
lake exe check-handles
lake env lean Audit.lean
```

Keep the supplied contracts and call wrappers fixed. Do not discharge obligations with
new axioms, `sorry`, or `admit`. Explain the write frame, preservation of executable code,
and transfer from a one-call theorem to a reusable persistent invariant. Include an agent
proposal you rejected or repaired, and explain why the final proof establishes the intended
claim without weakening it. Disclose reference material you consult.

The guarantee is about the supplied sequential RV64 model and host call convention.
It assumes exclusive access while the routine executes and does not establish hardware
correspondence, crash consistency, or concurrent safety. Preserving a functional snapshot
of old memory is not an implementation of transactions on physical hardware.

# Optional Extensions

1. Prove a full-or-overfull refusal theorem without `Buffer`, table-readability, or data-write
   premises. Keep the machine-word input bounds explicit. The core buffer invariant admits
   full tables but excludes overfull ones; the concrete robustness check is broader.
2. Prove correctness across a finite sequence of appends and lookups by composing the
   component contracts, rather than unrolling instruction traces.
3. Add a duplicate-reusing grant policy: return the first existing handle without changing
   the table, even when full; otherwise append if there is room. Specify refusal explicitly.
4. Add host-side growth and a proof that it preserves the logical view. Keep growth separate
   from the bounded native routine and explain when rebuilding an image is permitted.
