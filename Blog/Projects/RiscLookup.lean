import VersoBlog

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "projects/risc-lookup"

#doc (Page) "Project 7: Verified RISC Lookup" =>

Our preliminary projects developed specifications, representation invariants, machine
semantics, and refinement proofs. We now apply those ideas to a component of PL/OS: a
machine-code routine that looks up a channel in a handle table. You will write the assembly
and prove that its encoded execution implements a precise lookup specification.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/risc-lookup)
depends on a pinned version of PL/OS for the machine, assembler, and verification infrastructure.
It does not require solutions to earlier assignments. The implementation and correctness
proofs are your work; the supplied build checks the infrastructure, not a completed lookup.

# Build and Explore

From the repository root:

```
cd projects/risc-lookup
lake build
```

Open this directory as a Lean project. Lake downloads the dependencies on the first build;
you do not need a separate checkout of PL/OS. The package selects Lean 4.27.0.

- `RiscLookup/Spec.lean`: table representation, inputs, and observable result.
- `RiscLookup/Program.lean`: the assembly body you will implement and its encoded image.
- `RiscLookup/Exercises.lean`: the propositions you must prove.
- `RiscLookup/Support.lean`: helpers for fetching an installed instruction and excluding
  premature return.
- `RiscLookup/Fixtures.lean`: executable examples and candidate checks.
- `Checks.lean`: supplied infrastructure checks; import your solution here.
- `Audit.lean`: an entry point for reporting theorem assumptions.

Read the supplied upstream modules `Plos.RiscV.Model`, `Assembler`, `Code`, and `Call`.
Keep your implementation in the course namespace and import those infrastructure modules.
Do not import the completed upstream lookup or use its correctness theorem to discharge
your obligations. The reference development is public: explain any reference material
you consult and how you establish that your own program satisfies this assignment's contract.

# The Lookup Interface

A local handle is an index into a dense table of channel identifiers. This routine performs
the bounded table access; it does not establish whether the resulting channel is allocated
or whether a process has authority to use it. Those are obligations of its callers.

The calling convention is:

- On entry, `a0` holds the table address, `a1` its length, and `a2` the index.
- On a hit, return the channel in `a0` and one in `a1`.
- On a miss, return zero in both `a0` and `a1`.
- Return through `ra`. Preserve all memory, the privilege mode, and every architectural
  register except `a0`, `a1`, and `a2`.

All 64-bit channel values are permitted, including zero and values with the high bit set.
The found flag distinguishes a successful lookup of channel zero from a miss. Compare the
index and length as *unsigned* words. A word with its high bit set is not a negative index.

# Specify the Representation

```anchor table (module := RiscLookup.Spec)
/-- A nonwrapping sequence of readable 64-bit cells, with all word values allowed. -/
def Table (memory : Memory) (mode : Mode) (address : Word) (channels : List Word) : Prop :=
  address.toNat + 8 * channels.length ≤ 2^64 ∧
    ∀ index channel, channels[index]? = some channel →
      memory.load mode .read (address + BitVec.ofNat 64 (8 * index)) .double = .ok channel.toNat
```

The first conjunct prevents the abstract table from wrapping around the address space.
The second connects each logical entry to an actual successful load. A load checks
eight-byte alignment, backing-store bounds, and read permission for the entire cell.
The table predicate therefore includes more than agreement with raw bytes.

For an empty table, there are no cell-load obligations. Do not infer alignment or read
permission from the predicate when there are no entries.

# Specify the Result

```anchor result (module := RiscLookup.Spec)
/-- Observable lookup behavior, including termination and the complete read-only frame. -/
def Correct (channels : List Word) (index : Nat) (returnAddress : Word)
    (before : State) (result : CallResult) : Prop :=
  result.stop = .returned ∧ result.state.pc = returnAddress ∧
    result.retired ≤ 16 ∧ result.state.memory = before.memory ∧
    result.state.mode = before.mode ∧
    (∀ r : Register, r ≠ 10 → r ≠ 11 → r ≠ 12 →
      result.state.readReg r = before.readReg r) ∧
    match channels[index]? with
    | none => result.state.readReg 10 = 0 ∧ result.state.readReg 11 = 0
    | some channel => result.state.readReg 10 = channel ∧ result.state.readReg 11 = 1
```

The contract requires successful return within 16 retired instructions, with the correct
value and flag. The budget is independent of table length. You may use any instruction
sequence that meets the contract; no particular encoding or exact instruction count is required.

Preserving memory alone is insufficient: a routine that simply returns cannot implement
lookup. Conversely, producing the right value is insufficient if the routine damages
another register or returns only for some permitted inputs. The specification includes
the result, termination, and frame together.

# Installed Code and the Return Marker

Unlike the teaching machine's decoded instruction array, this model fetches instruction
bytes from permission-checked memory and decodes them before execution. `CodeAt` states
that an aligned, nonwrapping instruction image is executable at a chosen base address.
Its `step` lemma connects fetching and decoding a particular installed word to executing
the decoded instruction. Calling `execute` directly would bypass these checks.

```anchor returnMarker (module := RiscLookup.Spec)
/-- The harness must not mistake an instruction within the image for a completed call. -/
structure ReturnAt (base returnAddress : Word) (code : Array InstructionWord) : Prop where
  aligned : returnAddress.toNat % 4 = 0
  distinct : base ≠ returnAddress
  outside : returnAddress.toNat < base.toNat ∨
    base.toNat + 4 * code.size ≤ returnAddress.toNat
```

The call harness recognizes the return address before fetching an instruction or checking
fuel. The marker need not be mapped. It must be aligned, distinct from the entry, and
outside the routine, so the harness cannot mistake an intermediate PC for a completed call.
Its position depends on your code size, rather than a fixed reference implementation.

```anchor inputs (module := RiscLookup.Spec)
/-- Inputs describe a prepared machine state, immediately before the first instruction. -/
structure Inputs (code : Array InstructionWord) (state : State) (base ret : Word)
    (channels : List Word) (index : Nat) : Prop where
  image : CodeAt state.memory state.mode base code
  location : ReturnAt base ret code
  table : Table state.memory state.mode (state.readReg 10) channels
  lengthFits : channels.length < 2^64
  indexFits : index < 2^64
  entry : state.pc = base
  ra : state.readReg 1 = ret
  length : state.readReg 11 = BitVec.ofNat 64 channels.length
  index : state.readReg 12 = BitVec.ofNat 64 index
```

These assumptions describe the state *after call preparation*. The length and index must
fit in a word before conversion from natural numbers. Code may be installed at any permitted
base, and the return marker may be any permitted address. Your proof must not silently
specialize these locations to the concrete fixtures.

# Write and Assemble the Routine

```anchor starter (module := RiscLookup.Program)
/-- Replace the empty body with your assembly program. a0 = table, a1 = length, a2 = index.
Return through ra with a0 = value (zero on a miss), a1 = found. Only a0–a2 may change. -/
def program : List Assembler.Item := []

/-- Assembly must succeed by proof; do not replace errors with an empty image. -/
def code : Array InstructionWord :=
  (Assembler.assemble program).toOption.get (by decide +kernel)
```

Replace the empty body with assembly items. Use symbolic labels for branches and the
register aliases in `Assembler.Reg`. The relevant instructions include `bgeu`, `add`,
`addi`, `ld`, and `jalr`. The model has no multiply instruction: work out how to scale a
cell index by eight with the available arithmetic. Explain why the address computation
agrees with the table predicate, despite word arithmetic being modular.

Assembly produces real 32-bit instruction words. The proof in `code` establishes that
assembly succeeds; update that proof if necessary after editing the program. Do not
replace assembly failure with a default image. Inspect the decoded words as part of
your work, and prove the decoding facts needed by your execution argument.

# Prove Execution Correct

```anchor runCorrect (module := RiscLookup.Exercises)
/-- Prove this proposition for your assembled routine, at every permitted location and input. -/
def RunCorrect : Prop :=
  ∀ (state : State) (base ret : Word) (channels : List Word) (index fuel : Nat),
    Inputs code state base ret channels index → 16 ≤ fuel →
      Correct channels index ret state (resumeCall ret fuel state)
```

Prove this proposition in `RiscLookup/Solution.lean`. A useful progression is:

1. Separate the hit and miss cases of the abstract list lookup. Relate them to the
   unsigned branch condition using the word-fit assumptions.
2. Describe the register state and PC at the important instruction boundaries. Use
   `State.read_write`, `read_write_self`, and `read_write_other` rather than repeatedly
   expanding the register vector.
3. Use `CodeAt.step` or `Support.step_at` to justify each fetched and decoded instruction.
   For the hit, derive the successful data load from `Table`.
4. Build terminating traces using `Returns.done` and `Returns.step`. Use
   `Support.not_return` to exclude premature return at instruction positions and
   `Returns.run` to connect the traces to every sufficient fuel allowance.
5. Establish the result and frame in both cases. Track which registers are scratch
   registers and which values must survive until return.

A trace of only successful instructions proves that these admitted calls do not trap.
The fuel-bounded interpreter always terminates; the substantial claim is that the guest
routine reaches its specified return marker within the budget.

# Connect the Public Call Interface

```anchor callCorrect (module := RiscLookup.Exercises)
/-- Transfer the result to the public call interface; the frame starts after preparation. -/
def CallCorrect : Prop :=
  ∀ (call : Call) (original prepared : State) (channels : List Word) (index fuel : Nat),
    call.prepare original = .ok prepared →
    Inputs code prepared call.entry call.returnAddress channels index → 16 ≤ fuel →
      ∃ result, callRoutine call fuel original = .ok result ∧
        Correct channels index call.returnAddress prepared result
```

Prove this second proposition using your execution theorem and the definition of
`callRoutine`. `Call.prepare_spec` explains how preparation establishes the entry PC,
return address, stack pointer, and argument registers while retaining memory and mode.

The register frame compares the result to `prepared`, not `original`: preparation itself
sets `ra`, `sp`, and the argument registers. A leaf routine need not access the stack,
but call preparation still checks the supplied stack pointer's alignment.

# Run Concrete Checks

```anchor fixture (module := RiscLookup.Fixtures)
/-- Fixtures place code at 0 or 256 and data at 1024, with separate permissions. -/
def initial (image : Array InstructionWord) (base : Nat) (channels : List Word)
    (readable : Bool := true) : State := {
  registers := Vector.ofFn fun r => BitVec.ofNat 64 (1000 + r.val)
  memory := {
    bytes := Array.replicate base 0 ++ Assembler.bytes image ++
      Array.replicate (1024 - (base + 4 * image.size)) 0 ++ dataBytes channels
    regions := [⟨base, 4 * image.size, true, false, true, true⟩,
      ⟨1024, 8 * channels.length, readable, false, false, true⟩] } }

def invocation (image : Array InstructionWord) (base : Nat) (length index : Nat) : Call := {
  entry := BitVec.ofNat 64 base
  returnAddress := BitVec.ofNat 64 (base + 4 * image.size + 4)
  stackPointer := 0
  arguments := fun i => if i.val = 0 then 1024
    else if i.val = 1 then BitVec.ofNat 64 length
    else if i.val = 2 then BitVec.ofNat 64 index else 0 }
```

The fixtures use separate code and data permissions, recognizable initial register values,
and a return marker outside the image. Their fixed addresses are examples, not assumptions
in the universal correctness theorem.

After implementing the body, run:

```
lake exe check-lookup
```

This command intentionally fails for the empty starter. It checks empty and nonempty
tables, first and last entries, misses, channel zero, high-bit channels, the greatest
unsigned index, relocation to a nonzero code base, frames, and agreement across every
possible suspension boundary within the budget. It also checks misses without readable
table data. Candidate fixtures accept images of at most 128 instructions so code remains
separate from their data; this is a fixture limit, not an additional theorem hypothesis.

Resumption uses `resumeCall` on the saved state. Preparing the call again would reset
the arguments and restart execution. Return is recognized even when the final instruction
uses the last unit of fuel.

Passing these finite checks does not prove `RunCorrect` or `CallCorrect`. Add at least
one further check motivated by a bug you encountered or a plausible incorrect implementation.

# Submit and Explain

Submit your assembly, checked assembly and decoding facts, both correctness theorems,
additional check, and a short explanation of the proof. Import your solution from
`Checks.lean`, then run `lake build` and `lake env lean Audit.lean`. Add `#print axioms`
entries for your submitted theorems. Do not use new axioms, `sorry`, or `admit` to discharge
the obligations, and keep the supplied contracts fixed.

Explain the unsigned bounds check, address arithmetic, hit and miss traces, register frame,
and connection from assembly to encoded execution. Include your agent workflow: one
incorrect proposal or failed proof attempt, how you diagnosed it, and why the final repair
preserves the intended specification. A useful agent prompt asks for the PC and register
relationships that each proposed step lemma assumes and establishes.

These proofs establish behavior in the supplied sequential RV64 model. They rely on its
instruction semantics, permission checks, and host call convention. They do not establish
agreement with a physical processor, an operating-system ABI, or concurrent interference.

# Optional Extensions

1. Prove a separate miss theorem without the `Table` assumption. State the remaining
   assumptions precisely and show why no data load is needed, even for an unreadable or
   misaligned table address.
2. Prove that a suspended execution followed by sufficient additional fuel agrees with
   uninterrupted execution, including the sum of retired instructions. Generalize beyond
   the concrete fixture checks.
3. Strengthen the budget to the maximum number of instructions actually retired by your
   implementation, distinguishing hit and miss paths. Explain which choices affect it.
4. Specify a wrapper that distinguishes an invalid handle from an unallocated channel
   using a supplied allocation bound, and prove it agrees with the abstract resolution
   operation. The lookup theorem alone does not establish allocation validity.
