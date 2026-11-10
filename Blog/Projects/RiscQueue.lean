import VersoBlog

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "projects/risc-queue"

#doc (Page) "Project 9: A Runnable RISC Queue" =>

Project 2 represented a FIFO with a circular buffer. We now realize that representation
in native memory, with dequeue implemented by encoded RISC instructions and enqueue
reusing the verified cell-write mechanism from bounded append. We will connect the result
to PL/OS's runnable-queue interface, including the host policies that surround the bounded ring.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/risc-queue)
pins the same PL/OS revision as Projects 7 and 8. The append routine, generic memory lemmas,
loader, and host queue policy are supplied. You implement dequeue and the persistent
pop/push adapters, then prove their representation and interface contracts. No earlier
student solution is required.

# Build and Explore

From the repository root:

```
cd projects/risc-queue
lake build
```

Open this directory as a Lean project. It uses Lean 4.27.0 and downloads the pinned dependencies.

- `RiscQueue/Spec.lean`: standalone dequeue inputs and results.
- `RiscQueue/Program.lean`: the assembly body to implement.
- `RiscQueue/View.lean`: physical slots, logical FIFO view, and supplied arithmetic lemmas.
- `RiscQueue/Image.lean`: the verified loader for student dequeue code, supplied append, and data.
- `RiscQueue/Table.lean`: persistent ring state, validity, initialization, and readable-cell lemmas.
- `RiscQueue/Calls.lean`: argument layouts and return markers.
- `RiscQueue/Native.lean`: execution wrappers and the two adapter placeholders.
- `RiscQueue/Writer.lean`: the supplied proof that append writes one selected physical cell.
- `RiscQueue/API.lean`: the contracts required of a verified ring.
- `RiscQueue/Policy.lean`: supplied admission, growth, duplicate suppression, and removal policies.
- `RiscQueue/Exercises.lean`: required proof obligations.
- `RiscQueue/Fixtures.lean`, `Checks.lean`, and `Audit.lean`: examples, checks, and assumption reports.

You may use upstream `Append`, `Memory`, `TableUpdate`, and `Kernel.Components`. Do not
import the completed `RingPop`, `RingView`, `RingImage`, `Ring`, or `Kernel.NativeQueue`.
The audit rejects the completed dequeue and native ring/queue implementations.

# Separate Mechanism and Policy

The bounded ring stores word-sized values in FIFO order. It permits duplicates and has
fixed positive capacity. Dequeue reads one cell and changes metadata; enqueue writes an
unused tail cell. Neither operation needs to clear cells that are no longer active.

The kernel interface is broader. PIDs are natural numbers, enqueue suppresses an existing
PID, full queues can grow, and removal deletes every occurrence. The supplied host policy
handles those cases around the verified bounded mechanism. This separation lets us reuse
small native routines without pretending the entire scheduler runs as RISC code.

# Describe Physical and Logical State

```anchor view (module := RiscQueue.View)
/-- One wrap suffices for an active offset below capacity and a valid head. -/
def slot (head capacity offset : Nat) : Nat :=
  if head + offset < capacity then head + offset else head + offset - capacity

def words (cells : List Word) (head count capacity : Nat) : List Word :=
  let snapshot := cells.toArray
  (List.range count).map fun i => snapshot[slot head capacity i]!
```

`head` names the first active physical cell; `count` gives the number of active entries.
`slot head capacity offset` maps a logical offset to a physical index. One subtraction
suffices when both the head and offset are below capacity. The active sequence may cross
the end of the physical array.

For example, cells `[10, 20, 30, 40]`, head 3, and count 2 represent `[40, 10]`. After
popping 40, cell 3 still contains 40 but is inactive. A later push may reuse it. Stale
values outside the active sequence do not affect FIFO behavior; this is not a data-erasure guarantee.

```anchor viewLaws (module := RiscQueue.Exercises)
def ViewPop : Prop :=
  ∀ (cells : List Word) (head count capacity : Nat), head < capacity → count < capacity →
    View.words cells head (count+1) capacity =
      cells[head]! :: View.words cells (nextHead head capacity) count capacity

def ViewPush : Prop :=
  ∀ (cells : List Word) (head count capacity : Nat) (value : Word),
    cells.length = capacity → head < capacity → count < capacity →
      View.words (cells.set (View.slot head capacity count) value) head (count+1) capacity =
        View.words cells head count capacity ++ [value]
```

Prove these two properties before reasoning about assembly. `ViewPop` shifts the logical
head. `ViewPush` changes exactly the unused tail cell and extends the logical sequence.
Use the supplied slot bounds, injectivity, zero-offset, and next-head lemmas.

Injectivity explains why a write at logical offset `count` cannot overwrite an existing
active element when there is room. The full case is different: that offset would name
the head again. A caller must establish room before pushing.

# Specify Dequeue Before Implementing It

```anchor nextHead (module := RiscQueue.Spec)
def nextHead (head capacity : Nat) : Nat :=
  if head + 1 < capacity then head + 1 else 0
```

On entry, `a0` holds the buffer address, `a1` the head, `a2` the count, and `a3` the capacity.
On return, `a0` is the dequeued value, `a1` the next head, `a2` the next count, and `a3` a
found flag. You may use `a4` as scratch. Return through `ra`.

```anchor correct (module := RiscQueue.Spec)
/-- Dequeue returns a value and new metadata, with no memory writes. -/
def Correct (head count capacity : Nat) (value ret : Word) (before : State)
    (result : CallResult) : Prop :=
  result.stop = .returned ∧ result.state.pc = ret ∧ result.retired ≤ 16 ∧
    result.state.memory = before.memory ∧ result.state.mode = before.mode ∧
    (∀ r : Register, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 →
      result.state.readReg r = before.readReg r) ∧
    if count = 0 then
      result.state.readReg 10 = 0 ∧ (result.state.readReg 11).toNat = head ∧
      result.state.readReg 12 = 0 ∧ result.state.readReg 13 = 0
    else
      result.state.readReg 10 = value ∧
      (result.state.readReg 11).toNat = nextHead head capacity ∧
      (result.state.readReg 12).toNat = count - 1 ∧ result.state.readReg 13 = 1
```

On an empty dequeue, return zero and a false flag, retaining the head and zero count.
Do not access the data buffer. On a nonempty dequeue, read the old head cell, advance
the head with conditional wraparound, decrement the count, and return a true flag.
Zero is a valid stored value, so it cannot serve as the absence flag by itself.

Both cases preserve all memory, the privilege mode, and every register outside `a0`–`a4`.
The instruction budget is an upper bound; your implementation need not match the reference
encoding or its exact counts.

```anchor inputs (module := RiscQueue.Spec)
structure Inputs (code : Array InstructionWord) (state : State) (base ret address value : Word)
    (head count capacity : Nat) : Prop where
  image : CodeAt state.memory state.mode base code
  location : ReturnAt base ret code
  headBound : head < capacity
  countBound : count ≤ capacity
  capacityFits : capacity < 2^64
  cell : 0 < count → state.memory.load state.mode .read
    (address + BitVec.ofNat 64 (8*head)) .double = .ok value.toNat
  entry : state.pc = base
  ra : state.readReg 1 = ret
  address : state.readReg 10 = address
  head : state.readReg 11 = BitVec.ofNat 64 head
  count : state.readReg 12 = BitVec.ofNat 64 count
  capacity : state.readReg 13 = BitVec.ofNat 64 capacity
```

Only a nonempty call needs a readable head cell. The capacity and metadata bounds justify
converting natural numbers to words and interpreting the results back as natural numbers.
The installed code and external return marker justify execution through the real fetch
and decode path. The standalone theorem permits arbitrary valid code locations.

# Write and Prove the Encoded Routine

```anchor program (module := RiscQueue.Program)
/-- Implement dequeue: a0 = buffer, a1 = head, a2 = count, a3 = capacity.
Return a0 = value (zero if empty), a1 = new head, a2 = new count, a3 = found.
Only a0–a4 may change. Empty dequeue must not access the data buffer. -/
def program : List Assembler.Item := []

def code : Array InstructionWord :=
  (Assembler.assemble program).toOption.get (by decide +kernel)

/-- The supplied persistent layout reserves 24 words for dequeue. -/
theorem code_bound : code.size ≤ 24 := by decide +kernel
```

Implement the empty, ordinary nonempty, and wrapping nonempty paths. Use symbolic labels,
unsigned comparisons, and the model's load and arithmetic instructions. The supplied
persistent loader reserves at most 24 instruction words; update the checked assembly proof
and retain the size theorem as you develop your routine.

```anchor runCorrect (module := RiscQueue.Exercises)
def RunCorrect : Prop :=
  ∀ (state : State) (base ret address value : Word) (head count capacity fuel : Nat),
    Inputs code state base ret address value head count capacity → 16 ≤ fuel →
      Correct head count capacity value ret state (resumeCall ret fuel state)
```

Prove `RunCorrect` and `CallCorrect` in your solution module. Use `CodeAt.step`, terminating
`Returns` traces, and `Returns.run` to connect the encoded words to bounded execution.
`Support.not_return` excludes premature return at instruction positions. Treat the taken
wrap branch and the untaken branch explicitly, including the arithmetic bounds.

The empty path should not need a cell-load hypothesis. Its correctness still includes
termination and the full memory and register frames. Tests with an unreadable, misaligned
buffer address help expose implementations that touch data before checking emptiness.

# Maintain a Persistent Ring

```anchor ring (module := RiscQueue.Table)
/-- Persistent runtime state, with no shadow list of logical queue entries. -/
structure Ring where
  memory : Memory
  capacity : Nat
  head : Nat
  count : Nat
  deriving DecidableEq

namespace Ring

def cells (ring : Ring) : List Word :=
  (List.range ring.capacity).map fun i => BitVec.ofNat 64
    ((ring.memory.load .user .read (256 + BitVec.ofNat 64 (8*i)) .double).toOption.getD 0)

def words (ring : Ring) : List Word :=
  View.words ring.cells ring.head ring.count ring.capacity

def view (ring : Ring) : List Nat := ring.words.map BitVec.toNat

structure Valid (ring : Ring) : Prop where
  headBound : ring.head < ring.capacity
  countBound : ring.count ≤ ring.capacity
  base : ring.memory.base = 0
  size : ring.memory.bytes.size = 256 + 8*ring.capacity
  regions : ring.memory.regions = Image.regions code ring.capacity
  fits : 256 + 8*ring.capacity ≤ 2^64
  popCode : CodeAt ring.memory .user 0 code
  appendCode : Append.Code ring.memory .user 128
  represented : ∃ cells : List Word, cells.length = ring.capacity ∧
    Lookup.Table ring.memory .user 256 cells
```

The runtime state contains bytes and metadata, without a shadow logical queue. `cells`
decodes all physical slots; `words` selects the active FIFO; `view` converts those words
to natural-number PIDs. These views support specifications and host policies, but native
pop and push must execute against the retained image directly.

`Valid` connects the state to installed code, bounded metadata, memory permissions, and
a readable physical table. The existential cell sequence is proof-only. It covers the
entire capacity, including inactive cells, so every future tail slot is available.

```anchor init (module := RiscQueue.Table)
def init (values : List Word) (capacity : Nat) : Ring :=
  ⟨Image.memory code (padded values capacity) capacity, capacity, 0, values.length⟩

theorem init_valid (values : List Word) (capacity : Nat) (positive : 0 < capacity)
    (length : values.length ≤ capacity) (fits : 256 + 8*capacity ≤ 2^64) :
    (init values capacity).Valid :=
  ⟨positive, length, Image.memory_base _ _ _, Image.memory_size _ _ _,
    (by unfold init Image.memory; rfl), fits,
    Image.pop_code _ code_bound _ _, Image.append_code _ code_bound _ _,
    padded values capacity, padded_length _ _ length,
    Image.table _ code_bound _ _ (by rw [padded_length _ _ length]; exact Nat.le_refl _) fits⟩
```

Initialization pads unused cells with zero and starts at head zero. The supplied
`init_words` theorem establishes its logical view. Other supplied lemmas expose cell
loads, physical slot permissions, and nonwrapping addresses.

The fixed layout places dequeue at 0, append at 128, and data at 256. Both routines return
at marker 192. Code is executable but not writable; data is writable but not executable.

# Reuse Append as a Cell Writer

```anchor nativeCalls (module := RiscQueue.Native)
def popResult (ring : Ring) : CallResult := resumeCall 192 16 ring.popPrepared

def writePrepared (ring : Ring) (index : Nat) (value : Word) : State :=
  ((ring.writeCall index value).prepare { memory := ring.memory }).toOption.get (by
    simp [writeCall, Append.invocation, Call.prepare]; rfl)

/-- Bounded append writes one physical cell, with the physical index passed as its length. -/
def writeResult (ring : Ring) (index : Nat) (value : Word) : CallResult :=
  resumeCall 192 Append.allowance (ring.writePrepared index value)
```

The cell writer passes a *physical index* as append's length and the physical capacity as
its limit. It uses the readable prefix `cells.take index` to invoke append's contract.
The supplied `Writer` proofs establish return and an exact store effect for any valid
physical index. `Lookup.Table.set` transfers that effect to the complete physical table.

The writer's returned length is `index + 1`. It is not the ring's new logical count.
Your push adapter must retain the old head and set count to the old count plus one.
This is a case where reusing a verified component requires interpreting its interface
under a different representation.

```anchor adapters (module := RiscQueue.Native)
/-- Implement using the encoded dequeue result's value, head, and count. -/
def pop (ring : Ring) : Word × Ring := (0, ring)

/-- Implement using the verified write at the unused tail slot; retain its resulting memory. -/
def push (ring : Ring) (_value : Word) : Ring := ring
```

Implement both adapters. Pop takes the value, head, and count from the encoded dequeue
result, retaining capacity and memory. Push computes the unused tail slot, invokes the
supplied writer, and retains its resulting memory. Neither may rebuild an image from
`words` or silently fall back to a list implementation.

```anchor popCorrect (module := RiscQueue.API)
structure PopCorrect (ring : Ring) : Prop where
  returned : ring.popResult.stop = .returned
  found : ring.popResult.state.readReg 13 = 1
  value : ring.pop.1 = ring.popResult.state.readReg 10
  valid : ring.pop.2.Valid
  memory : ring.pop.2.memory = ring.memory
  capacity : ring.pop.2.capacity = ring.capacity
  head : ring.pop.2.head = (ring.popResult.state.readReg 11).toNat
  count : ring.pop.2.count = (ring.popResult.state.readReg 12).toNat
  words : ring.pop.1 :: ring.pop.2.words = ring.words
```

```anchor pushCorrect (module := RiscQueue.API)
structure PushCorrect (ring : Ring) (value : Word) : Prop where
  returned :
    (ring.writeResult (View.slot ring.head ring.capacity ring.count) value).stop = .returned
  valid : (ring.push value).Valid
  memory : (ring.push value).memory =
    (ring.writeResult (View.slot ring.head ring.capacity ring.count) value).state.memory
  capacity : (ring.push value).capacity = ring.capacity
  head : (ring.push value).head = ring.head
  count : (ring.push value).count = ring.count + 1
  cells : (ring.push value).cells =
    ring.cells.set (View.slot ring.head ring.capacity ring.count) value
  words : (ring.push value).words = ring.words ++ [value]
```

Prove `NativePopCorrect` and `NativePushCorrect`. For pop, use your execution theorem,
memory preservation, and `ViewPop`. For push, use `write_effect`, `Lookup.Table.set`,
`CodeAt.store64`, and `ViewPush`. Preserve both installed code images after the write.
Establish the concrete memory and metadata equalities as well as the logical FIFO result.

# Build the Verified Interface

```anchor correctRing (module := RiscQueue.API)
/-- A proof bundle to construct from student theorems, never an assumed axiom. -/
structure CorrectRing : Prop where
  pop : ∀ ring : Ring, ring.Valid → 0 < ring.count → PopCorrect ring
  push : ∀ (ring : Ring) (value : Word), ring.Valid → ring.count < ring.capacity →
    PushCorrect ring value
```

Construct a theorem named `verifiedRing : CorrectRing` from your actual pop and push
proofs. This bundle is a proposition: it supplies proof evidence to the host adapter,
not another runtime implementation or an assumed API. The unfinished starter does not
provide an inhabitant of this proposition.

The supplied policy carries validity evidence with each native ring. It can therefore
construct its next native state using the preservation fields of `verifiedRing`.
This keeps its kernel interface defined on every constructible queue value, without
adding a validity premise to every kernel queue operation.

# Refine the Runnable-Queue Policy

```anchor queue (module := RiscQueue.Policy)
/-- Native states carry validity evidence; fallback preserves arbitrary natural-number PIDs. -/
inductive Queue where
  | native (ring : Ring) (valid : ring.Valid)
  | fallback (pids : List Nat)

def view : Queue → List Nat
  | .native ring _ => ring.view
  | .fallback pids => pids

/-- Admission and growth occur on the host; no unrepresentable PID is silently truncated. -/
def fromList (pids : List Nat) : Queue :=
  let capacity := max 4 (2*pids.length)
  if fits : 256 + 8*capacity ≤ 2^64 ∧ pids.all (fun pid => decide (pid < 2^64)) = true then
    .native (Ring.init (pids.map (BitVec.ofNat 64)) capacity)
      (Ring.init_valid _ _ (by omega) (by simp only [List.length_map]; omega) fits.1)
  else .fallback pids
```

Admission chooses native storage when the image size and all PIDs fit, and otherwise
retains an exact list fallback. Test representability *before* conversion to a word.
An oversized natural-number PID must not wrap to another PID.

```anchor enqueue (module := RiscQueue.Policy)
def pushFresh (correct : CorrectRing) : Queue → Nat → Queue
  | .native ring valid, pid =>
    if room : ring.count < ring.capacity ∧ pid < 2^64 then
      .native (ring.push (BitVec.ofNat 64 pid)) (correct.push ring _ valid room.1).valid
    else .fallback (ring.view ++ [pid])
  | .fallback pids, pid => .fallback (pids ++ [pid])

def enqueue (correct : CorrectRing) (queue : Queue) (pid : Nat) : Queue :=
  if (Plos.Kernel.RunQueue.contains ⟨view queue⟩ pid) then queue
  else pushFresh correct (reserve queue) pid
```

The duplicate check comes before reserve or growth: enqueueing an existing PID retains
the exact queue value, including a full native buffer. A fresh word-sized PID in a
nonfull native ring uses the verified tail write. Growth is a host operation that
linearizes the logical FIFO into a larger image.

```anchor dequeue (module := RiscQueue.Policy)
def dequeue (correct : CorrectRing) : Queue → Option (Nat × Queue)
  | .fallback [] => none
  | .fallback (pid :: rest) => some (pid, .fallback rest)
  | .native ring valid =>
    if empty : ring.count = 0 then none
    else some (ring.pop.1.toNat, .native ring.pop.2 (correct.pop ring valid (by omega)).valid)

def remove (queue : Queue) (pid : Nat) : Queue :=
  fromList ((view queue).filter (fun p => decide (p ≠ pid)))

def isEmpty : Queue → Bool
  | .native ring _ => ring.count == 0
  | .fallback pids => pids.isEmpty
```

The host checks count for an empty native queue. A nonempty native dequeue uses the
value and state returned by your pop adapter. Removal is also host policy: filter the
logical view and rebuild a checked image. It removes *all* occurrences.

Validity does not require uniqueness. A queue admitted from `[1, 2, 1]` must retain that
meaning, dequeue in that order, and remove both ones when asked. Duplicate suppression
prevents adding another occurrence; it does not repair preexisting duplicates. Any stronger
uniqueness claim belongs in a separate whole-kernel invariant.

```anchor policyLaws (module := RiscQueue.Exercises)
def AdmissionCorrect : Prop := ∀ pids : List Nat, Policy.view (Policy.fromList pids) = pids

def PolicyCorrect : Prop :=
  ∀ correct : CorrectRing,
    (∀ (queue : Policy.Queue) (pid : Nat),
      Policy.view (Policy.enqueue correct queue pid) =
        (Plos.Kernel.RunQueue.enqueue ⟨Policy.view queue⟩ pid).pids) ∧
    (∀ queue : Policy.Queue,
      (Policy.dequeue correct queue).map (fun (pid, rest) => (pid, Policy.view rest)) =
        (Policy.view queue).head?.map (fun pid => (pid, (Policy.view queue).tail))) ∧
    (∀ (queue : Policy.Queue) (pid : Nat),
      Policy.view (Policy.remove queue pid) =
        (Policy.view queue).filter (fun p => decide (p ≠ pid))) ∧
    (∀ queue : Policy.Queue, Policy.isEmpty queue = (Policy.view queue).isEmpty)

def KernelContract : Prop :=
  ∀ correct : CorrectRing,
    ∃ contract : Plos.Kernel.Components.QueueContract (Policy.ops correct),
      contract.view = Policy.view
```

Prove admission preserves arbitrary lists, then derive the queue laws through the
ring's logical-view contracts. Construct the actual `Kernel.Components.QueueContract`
with `Policy.view` as its interpretation. Keep this argument at the component level;
do not replay instruction traces to prove enqueue or dequeue policy correctness.

```anchor nativeUse (module := RiscQueue.Exercises)
def NativeUse : Prop :=
  ∀ correct : CorrectRing,
    (∀ (queue : Policy.Queue) (pid : Nat),
      Plos.Kernel.RunQueue.contains ⟨Policy.view queue⟩ pid = true →
        Policy.enqueue correct queue pid = queue) ∧
    (∀ (ring : Ring) (valid : ring.Valid) (pid : Nat),
      Plos.Kernel.RunQueue.contains ⟨ring.view⟩ pid = false →
      ∀ (room : ring.count < ring.capacity), pid < 2^64 →
        Policy.enqueue correct (.native ring valid) pid =
          .native (ring.push (BitVec.ofNat 64 pid)) (correct.push ring _ valid room).valid) ∧
    (∀ (ring : Ring) (valid : ring.Valid) (nonempty : 0 < ring.count),
      Policy.dequeue correct (.native ring valid) =
        some (ring.pop.1.toNat, .native ring.pop.2 (correct.pop ring valid nonempty).valid))

/-- Exhibit the completed ring proof and its concrete kernel contract; do not assume the API. -/
def Integrated : Prop :=
  ∃ correct : CorrectRing,
    ∃ contract : Plos.Kernel.Components.QueueContract (Policy.ops correct),
      contract.view = Policy.view
```

Prove the native-use properties as well as abstract refinement. They record exact duplicate
reuse and the native paths taken for fresh enqueue and nonempty dequeue. `Integrated`
requires you to exhibit both the completed ring proof and its kernel contract. A theorem
that merely assumes `CorrectRing` is useful for composition, but is not a complete submission.

The queue contract is the interface consumed by PL/OS's generic storage-replacement proof.
Explain how it lets the kernel substitute this queue while retaining reference behavior,
and what additional theorem application would establish equivalence of whole executions.
Constructing the component contract alone is not that whole-execution theorem.

# Check Executions and Sequences

After implementing dequeue and the two adapters:

```
lake exe check-queue
```

This command intentionally fails on the starter. It checks empty and nonempty calls,
wraparound, capacity one, zero and maximum-word values, relocation, frames, and all fuel
splits within the budget. Ring checks start with wrapped storage, pop an entry, reuse
inactive cells with pushes, fill the ring, and empty it again. They compare adapter
results to native execution and the logical FIFO after updates.

After constructing `verifiedRing`, include this in your solution module:

```
#guard Course.RiscQueue.Fixtures.policyChecks verifiedRing
```

The policy checks exercise duplicates, removal of every matching PID, growth, FIFO order,
emptying, and fallback for an oversized PID. They require your proof bundle so the supplied
policy can construct valid native states. The ordinary starter build checks the loader,
cell writer, views, and admission examples; it does not complete the student obligations.

Add a regression check for a bug or plausible incorrect implementation you encountered.
Explain a trace that crosses the physical wrap boundary and why its logical order remains FIFO.

# Submit and Explain

Implement `program`, `Ring.pop`, and `Ring.push`. Create `RiscQueue/Solution.lean`, importing
`RiscQueue.Fixtures`, with proofs of `ViewPop`, `ViewPush`, `RunCorrect`, `CallCorrect`,
`NativePopCorrect`, `NativePushCorrect`, `AdmissionCorrect`, `PolicyCorrect`, `KernelContract`,
`NativeUse`, and `Integrated`, together with your constructed `verifiedRing` bundle.
Import the solution from `Checks.lean` and add its theorem-assumption reports to `Audit.lean`.

```
lake build
lake exe check-queue
lake env lean Audit.lean
```

Keep the supplied contracts, execution wrappers, writer, and policy fixed. Do not use
new axioms, `sorry`, or `admit`. Explain the physical/logical distinction, reuse of append,
preservation of code and inactive cells, and each boundary between native mechanism and host
policy. Disclose reference material and describe one agent-generated error you diagnosed
without weakening the intended claim.

These guarantees concern the supplied sequential model under exclusive access. They do
not prove concurrent queue safety, interrupt handling, hardware correspondence, scheduler
fairness, or erasure of inactive data.

# Optional Extensions

1. Instantiate PL/OS's generic storage-replacement theorem with the completed queue contract
   and standard other components. State the related initial states and bounded execution
   budgets explicitly, then prove whole-kernel execution refinement.
2. Prove the ring laws for finite mixed operation sequences using the component contracts.
3. Strengthen the empty-call theorem to remove unnecessary metadata bounds, while keeping
   the encoded input interpretation precise and requiring no readable buffer.
4. Implement removal or duplicate detection as a verified RISC loop, replacing one host
   policy step while preserving the same kernel contract.
