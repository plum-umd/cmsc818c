import VersoBlog
import ProtectedMemory
import ProtectedMemory.Examples

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "."

#doc (Page) "Project 5: Protected Memory and Isolation" =>

Correctness includes respecting limits on authority. A store may encode the right value at
the right address and still be a serious security flaw if the caller has no right to modify
that memory. In this project, we specify a protected-memory service and prove that operations
by one domain cannot modify another domain's protected bytes.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/protection) contains
an executable model, an independent access and byte-update specification, regression checks,
and proof obligations. No previous project solution is required.

# Build and Explore

From the repository root:

```
cd projects/protection
lake build
```

The modules separate policy, implementation, and reasoning:

- `ProtectedMemory/Model.lean`: domains, regions, memory, access checking, byte encoding,
  commands, operations, and command sequences.
- `ProtectedMemory/Semantics.lean`: permitted checks and steps, including failed accesses
  and an extensional specification of byte updates.
- `ProtectedMemory/Exercises.lean`: the correctness and isolation obligations.
- `ProtectedMemory/Support.lean`: supplied array-size and byte-reconstruction lemmas.
- `ProtectedMemory/Examples.lean` and `Checks.lean`: concrete configurations and executions.

The starter builds, but its exercise propositions are not proofs of the required guarantees.

# Describe Memory and Authority

```anchor memoryPolicy (module := ProtectedMemory.Model)
inductive Domain where
  | left | right
  deriving DecidableEq, Repr

inductive Access where
  | read | write
  deriving DecidableEq, Repr

structure Region where
  start : Nat
  size : Nat
  owner : Domain
  readable : Bool
  writable : Bool
  deriving DecidableEq, Repr

def Region.finish (region : Region) : Nat := region.start + region.size

structure Memory where
  base : Nat
  bytes : Array UInt8
  regions : List Region
  deriving DecidableEq, Repr

def Memory.finish (memory : Memory) : Nat := memory.base + memory.bytes.size
```

Memory is a finite array of bytes at an absolute byte address. A region describes a half-open
interval, its owner, and read/write permissions. There are two domains, `left` and `right`.
Addresses and transferred values are 64-bit words; range calculations use natural numbers.

The host selects the domain for each invocation. Commands do not contain a domain field and
cannot alter the policy. Supplying a domain argument is not authentication: an embedding must
ensure that a client cannot invoke the service as another domain. We assume that host boundary
here, rather than modeling how callers are identified.

## Authorize the Entire Access

```anchor accessSpecification (module := ProtectedMemory.Model)
def Region.Covers (region : Region) (domain : Domain) (access : Access) (address : Word) : Prop :=
  region.owner = domain ∧ region.start ≤ address.toNat ∧
    address.toNat + width ≤ region.finish ∧ address.toNat + width ≤ addressLimit ∧
    (match access with | .read => region.readable | .write => region.writable) = true

instance (region : Region) (domain : Domain) (access : Access) (address : Word) :
    Decidable (region.Covers domain access address) := by
  unfold Region.Covers
  infer_instance

def Allowed (memory : Memory) (domain : Domain) (access : Access) (address : Word) : Prop :=
  ∃ region ∈ memory.regions, region.Covers domain access address

def Backed (memory : Memory) (address : Word) : Prop :=
  memory.base ≤ address.toNat ∧ address.toNat + width ≤ memory.finish ∧
    address.toNat + width ≤ addressLimit

instance (memory : Memory) (address : Word) : Decidable (Backed memory address) := by
  unfold Backed
  infer_instance
```

Each operation accesses eight bytes and must be aligned to eight bytes. A single region must
authorize the entire interval `[address, address + 8)`. Authorizing just its first byte is
insufficient. Permissions from two adjacent regions are not combined, even if their owner is
the same. This gives an explicit, conservative rule for boundary-crossing accesses.
Permissions are grants: any single matching region suffices. A false flag on another
overlapping region does not override an existing grant.

`Allowed` describes authority; `Backed` describes storage. Permission does not conjure backing
bytes into existence. Conversely, the presence of bytes does not authorize their use.
The end calculations must not wrap past `2^64`.

## State the Policy Assumptions

```anchor validPolicy (module := ProtectedMemory.Model)
def Isolated (regions : List Region) : Prop :=
  ∀ left ∈ regions, ∀ right ∈ regions, left.owner ≠ right.owner →
    left.finish ≤ right.start ∨ right.finish ≤ left.start

def Memory.Valid (memory : Memory) : Prop :=
  memory.finish ≤ addressLimit ∧
  (∀ region ∈ memory.regions, memory.base ≤ region.start ∧ region.finish ≤ memory.finish) ∧
  Isolated memory.regions

def Owned (memory : Memory) (domain : Domain) (address : Nat) : Prop :=
  ∃ region ∈ memory.regions,
    region.owner = domain ∧ region.start ≤ address ∧ address < region.finish

def byteAt (memory : Memory) (address : Nat) : Option UInt8 :=
  if memory.base ≤ address then memory.bytes[address - memory.base]? else none
```

`Memory.Valid` requires backing storage within the address space, regions within the backing
interval, and disjoint regions whenever their owners differ. Regions with the same owner may
overlap. `Owned` designates a domain's bytes independently of whether its current access flags
permit reading or writing them.

`byteAt` observes an absolute byte address, returning `none` when it is outside the backing
storage. It lets isolation statements compare memory contents without exposing array indices.

The host must establish validity of the initial configuration. The service still has defined
behavior on invalid configurations, but isolation is not promised for them. For example, if
both domains are granted ownership of the same interval, checking that a write is authorized
does not prevent it from changing bytes also designated as belonging to the other domain.

# Specify Checks and Their Failure Priority

```anchor checkSemantics (module := ProtectedMemory.Semantics)
inductive CheckSpec (memory : Memory) (domain : Domain) (access : Access) (address : Word) :
    Except Fault Nat → Prop where
  | misaligned (bad : address.toNat % width ≠ 0) : CheckSpec memory domain access address
      (.error .misaligned)
  | denied (aligned : address.toNat % width = 0) (denied : ¬ Allowed memory domain access address) :
      CheckSpec memory domain access address (.error .accessDenied)
  | outside (aligned : address.toNat % width = 0) (allowed : Allowed memory domain access address)
      (outside : ¬ Backed memory address) :
      CheckSpec memory domain access address (.error .outOfBounds)
  | ready (aligned : address.toNat % width = 0) (allowed : Allowed memory domain access address)
      (backed : Backed memory address) : CheckSpec memory domain access address
        (.ok (address.toNat - memory.base))
```

These rules specify the result before we examine the checker. Misalignment takes priority
over access denial. For an aligned request, lack of authority produces `accessDenied`.
An authorized request without backing produces `outOfBounds`. Only the final rule permits
an array offset to be returned.

Although a valid policy places every region within backing memory, the backing check remains
explicit and protects the executable service even when given an invalid configuration.
Students will prove conformance for all configurations and use validity as a separate
assumption when establishing isolation.

# Specify Byte Contents and State Changes

```anchor byteSpecification (module := ProtectedMemory.Semantics)
def SameLayout (before after : Memory) : Prop :=
  after.base = before.base ∧ after.regions = before.regions ∧ after.bytes.size = before.bytes.size

def Loaded (memory : Memory) (offset : Nat) (value : Word) : Prop :=
  ∀ index : Nat, index < width → memory.bytes[offset + index]? = some (byteOf value index)

def Stored (before after : Memory) (offset : Nat) (value : Word) : Prop :=
  SameLayout before after ∧
  ∀ index : Nat, index < before.bytes.size →
    after.bytes[index]? =
      if offset ≤ index ∧ index < offset + width then some (byteOf value (index - offset))
      else before.bytes[index]?
```

`Loaded` requires the returned word's eight little-endian bytes to equal the backing bytes.
`Stored` specifies the whole update: base, policy, and array size stay fixed; exactly the
designated byte interval gets the encoded value; every other array entry stays unchanged.
It does not refer to the implementation's `writeWord` function.

`SameLayout` is crucial for later calls. A service that preserves payload bytes but changes
the permissions or reinterprets their base address would not preserve the same protection
boundary.

```anchor operationSemantics (module := ProtectedMemory.Semantics)
inductive Step (domain : Domain) : Memory → Command → Reply → Memory → Prop where
  | failure (failed : CheckSpec memory domain command.access command.address (.error reason)) :
      Step domain memory command (.fault reason) memory
  | load (checked : CheckSpec memory domain .read address (.ok offset))
      (decoded : Loaded memory offset value) :
      Step domain memory (.load address) (.loaded value) memory
  | store (checked : CheckSpec before domain .write address (.ok offset))
      (updated : Stored before after offset value) :
      Step domain before (.store address value) .stored after

inductive Trace (domain : Domain) : Memory → List Command → List Reply → Memory → Prop where
  | nil : Trace domain memory [] [] memory
  | cons (first : Step domain before command reply middle)
      (rest : Trace domain middle commands replies after) :
      Trace domain before (command :: commands) (reply :: replies) after
```

`Step` combines access checks with the byte specification. A failed operation returns the
entire original memory. A load returns a word without changing memory. A successful store
must satisfy the extensional update relation. `Trace` composes steps under a fixed caller
domain, carrying every reply and intermediate memory state.

# Implement the Checked Service

```anchor checkAccess (module := ProtectedMemory.Model)
def check (memory : Memory) (domain : Domain) (access : Access) (address : Word) :
    Except Fault Nat :=
  if address.toNat % width ≠ 0 then .error .misaligned
  else if memory.regions.any (fun region => decide (region.Covers domain access address)) then
    if Backed memory address then .ok (address.toNat - memory.base)
    else .error .outOfBounds
  else .error .accessDenied
```

The checker searches for a region covering the whole access. It converts to an array offset
only after checking authority and backing. Your conformance proof must connect the Boolean
search through the region list to the existential proposition `Allowed`.

```anchor byteEncoding (module := ProtectedMemory.Model)
def byteOf (value : Word) (index : Nat) : UInt8 :=
  UInt8.ofNat (value.toNat / 2 ^ (8 * index))

def readWord (bytes : Array UInt8) (offset : Nat) : Word :=
  BitVec.ofNat 64 <| (List.range width).foldl
    (fun value index => value + (bytes[offset + index]?.getD 0).toNat * 2 ^ (8 * index)) 0

def writeWord (bytes : Array UInt8) (offset : Nat) (value : Word) : Array UInt8 :=
  (List.range width).foldl
    (fun bytes index => bytes.setIfInBounds (offset + index) (byteOf value index)) bytes
```

Byte zero is the least significant byte. `readWord` combines eight bytes with powers of 256;
`writeWord` writes those bytes individually. These helpers are total even for invalid offsets:
an optional read has a default, and an out-of-bounds update has no effect. Those defaults
do not make such accesses correct. Successful checking must establish that all eight positions
exist, so no successful operation relies on a default or silently skipped update.

```anchor operations (module := ProtectedMemory.Model)
inductive Command where
  | load (address : Word)
  | store (address value : Word)
  deriving DecidableEq, Repr

def Command.access : Command → Access
  | .load _ => .read
  | .store .. => .write

def Command.address : Command → Word
  | .load address | .store address _ => address

inductive Reply where
  | loaded (value : Word)
  | stored
  | fault (reason : Fault)
  deriving DecidableEq, Repr

def operate (memory : Memory) (domain : Domain) (command : Command) : Reply × Memory :=
  match command with
  | .load address =>
      match check memory domain .read address with
      | .error reason => (.fault reason, memory)
      | .ok offset => (.loaded (readWord memory.bytes offset), memory)
  | .store address value =>
      match check memory domain .write address with
      | .error reason => (.fault reason, memory)
      | .ok offset => (.stored, { memory with bytes := writeWord memory.bytes offset value })

def runTrace (memory : Memory) (domain : Domain) : List Command → List Reply × Memory
  | [] => ([], memory)
  | command :: commands =>
      let (reply, next) := operate memory domain command
      let (replies, final) := runTrace next domain commands
      (reply :: replies, final)
```

`operate` performs every check before invoking the byte-writing helper. It returns a reply
and next memory explicitly. A fault leaves the whole memory unchanged; no prefix of a rejected
store is committed. `runTrace` continues after faults using that unchanged state and records
the fault reply. A failed command does not erase earlier successful stores.

# Try Two Domains

```anchor exampleMemory (module := ProtectedMemory.Examples)
def initial : Memory := {
  base := 0x1000
  bytes := Array.replicate 32 0
  regions := [
    ⟨0x1000, 16, .left, true, true⟩,
    ⟨0x1010, 16, .right, true, true⟩] }
```

Each domain owns sixteen bytes. An aligned store at `0x1000` belongs to `left`; an aligned
store at `0x1010` belongs to `right`. The following executions are checked with the page:

```leanInit protectionProject
```

```lean protectionProject
open Course.ProtectedMemory Course.ProtectedMemory.Examples

example : operate initial .right (.store 0x1000 7) =
    (.fault .accessDenied, initial) := by decide

example :
    let result := runTrace initial .left
      [.store 0x1000 7, .store 0x1010 99, .load 0x1000, .load 0x1010]
    result.1 = [.stored, .fault .accessDenied, .loaded 7, .fault .accessDenied] ∧
      result.2.bytes[16]? = initial.bytes[16]? := by decide
```

The attempted write into the other domain fails. The earlier authorized write remains,
and reading it returns 7. The private byte at array index 16 remains unchanged. The exercise
is to establish corresponding facts for arbitrary values, addresses, and finite command lists.

# The Isolation Goals

```anchor isolationGoals (module := ProtectedMemory.Exercises)
def StepIsolation : Prop :=
  ∀ (before after : Memory) (actor owner : Domain) (command : Command) (reply : Reply),
    before.Valid → actor ≠ owner → Step actor before command reply after →
    ∀ address : Nat, Owned before owner address → byteAt after address = byteAt before address

def TraceIsolation : Prop :=
  ∀ (memory : Memory) (actor owner : Domain) (commands : List Command),
    memory.Valid → actor ≠ owner →
    ∀ address : Nat, Owned memory owner address →
      byteAt (runTrace memory actor commands).2 address = byteAt memory address
```

First prove isolation for a step permitted by the specification. The load and failure rules
preserve memory directly. For a store, use the authorized region, the cross-domain disjointness
assumption, and the byte-frame clause of `Stored` to show that another owner's byte cannot be
among the bytes updated.

Then transfer the result to the executable service and compose it across commands. The trace
proof must maintain validity and policy identity at every step. It is not enough to observe
that one store stayed within its footprint: the permission configuration and interpretation
of addresses must also remain stable for the next call.

This is an integrity guarantee. It prevents modification of protected bytes. It does not by
itself prove that an observer learns nothing about them.

# Core Assignment

1. *Understand the policy.* Explain `Allowed`, `Backed`, and `Owned`. Establish validity of
   the example configuration. Construct an overlapping-ownership configuration and demonstrate
   why local permission checks alone do not establish isolation without the validity hypothesis.
2. *Prove safety of the specification.* Prove `Exercises.StepPreservation` and
   `Exercises.StepIsolation` by cases on `Step`. Make explicit how `Stored` preserves layout
   and how disjoint regions prevent another owner's byte from falling within a store interval.
3. *Connect checking and encoding to the specification.* Prove `Exercises.CheckCorrect`,
   `Exercises.ReadCorrect`, and `Exercises.WriteCorrect`. Account for whole-access bounds,
   little-endian byte order, and unchanged bytes. The starter supplies `Support.writeWord_size`
   and `Support.byte_roundtrip`; you may use those lemmas without reproving them.
4. *Verify individual operations.* Prove `Exercises.OperateCorrect`,
   `Exercises.FailureAtomicity`, `Exercises.LayoutPreservation`, `Exercises.Preservation`,
   and `Exercises.StoreFrame`. Prove `Exercises.LoadAfterStore`; note that write permission
   alone does not imply read permission, so its statement requires both checks to succeed.
5. *Compose protection over time.* Prove `Exercises.TraceCorrect` and
   `Exercises.TraceIsolation`. Use specification preservation, step isolation, and conformance
   to relate each concrete operation to a permitted step and maintain the invariant.

Create `ProtectedMemory/Solution.lean`, import the supplied modules, and import your solution
from `Checks.lean`. Keep the given policy, executable functions, and exercise propositions
fixed. Tests should include a partially covered access, a read-only region, a denied write,
an unbacked authorized range, and the last aligned word in the address space.

Submit the proofs with an explanation of the trusted host boundary, policy assumptions,
failure priority, and trace invariant. Distinguish integrity from confidentiality and explain
why preserving permissions is part of the argument. Audit theorem dependencies following
`Audit.lean`; do not introduce axioms or proof placeholders. Ask an agent to identify the
region authorizing a store and the region protecting a byte before attempting the isolation
proof, rather than assuming those regions cannot overlap.

# Optional Extensions

## Confidentiality of Replies

```anchor confidentialityGoal (module := ProtectedMemory.Exercises)
def VisibleEqual (domain : Domain) (left right : Memory) : Prop :=
  SameLayout left right ∧
    ∀ address : Nat, Owned left domain address → byteAt left address = byteAt right address

def RepliesIndependent : Prop :=
  ∀ (left right : Memory) (domain : Domain) (commands : List Command),
    left.Valid → right.Valid → VisibleEqual domain left right →
      (runTrace left domain commands).1 = (runTrace right domain commands).1
```

`VisibleEqual` requires identical layout and equal contents in the observing domain's regions.
Other bytes may differ. Prove `RepliesIndependent`: running the same command list in the two
memories produces the same replies. Invalid requests must also have indistinguishable replies;
the checker must not inspect denied payloads before deciding whether to reject an access.

This compares observations in the model: returned values and faults for a fixed finite command
list. It does not establish protection against execution-time, cache, speculative-execution,
or other hardware side channels. Nor does it model concurrent interference.

## Machine Integration

Extend the small RISC machine with load and store instructions backed by this service. Specify
how the active domain is chosen, how a fault affects the PC and registers, and how successful
memory operations relate to the machine step. Verify a short routine and its memory-frame
property. Reuse the byte and access guarantees rather than treating successful instructions
as arbitrary memory updates.

Dynamic allocation, policy changes, context switching, and shared regions remain outside the
core project. Adding them requires stating how authority can change and which parts of the
isolation argument must be re-established.
