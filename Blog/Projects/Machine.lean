import VersoBlog
import MiniRisc

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "."

#doc (Page) "Project 3: A Small RISC Machine" =>

The first two projects reason about functions that operate on data structures. This project
introduces programs whose behavior is a sequence of machine instructions. We will specify
individual steps, connect an executable interpreter to that specification, and verify a
loop with a precise result, termination argument, and register-frame property.

The [starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/machine) is
self-contained. You do not need solutions to the earlier projects.

# Build and Explore

From the repository root:

```
cd projects/machine
lake build
```

Open this directory as a Lean project. The modules divide the work as follows:

- `MiniRisc/Model.lean`: words, registers, programs, fetching, instruction execution, and a runner.
- `MiniRisc/Semantics.lean`: successful instruction rules, fault rules, and finite executions.
- `MiniRisc/Countdown.lean`: the small program we will verify.
- `MiniRisc/Exercises.lean`: the correctness statements students must prove.
- `MiniRisc/Support.lean`: a supplied arithmetic lemma for the termination argument.
- `Checks.lean`: concrete checks for arithmetic, branches, fetch faults, fuel, and resumption.

The supplied executable definitions and checks build. Most correctness properties are
exercise propositions, not supplied theorems. A passing starter build does not complete them.

# The Machine State

```anchor machineState (module := MiniRisc.Model)
abbrev Word := BitVec 64
abbrev Register := Fin 32

structure State where
  registers : Vector Word 32 := Vector.replicate 32 0
  pc : Word := 0
  deriving DecidableEq, Repr

def State.readReg (state : State) (register : Register) : Word :=
  if register.val = 0 then 0 else state.registers[register.val]

def State.writeReg (state : State) (register : Register) (value : Word) : State :=
  if register.val = 0 then state
  else { state with registers := state.registers.set register.val value register.isLt }
```

There are 32 registers, each holding a 64-bit word, and a program counter `pc`. A `Register`
is a bounded index: `Fin 32` prevents referring to a nonexistent register. Register zero
always reads as zero and ignores writes, even if its backing vector slot contains another
value. Distinguish architectural reads through `readReg` from inspecting the vector directly.

Words use arithmetic modulo `2^64`. For example, adding one to the greatest unsigned word
produces zero. This behavior also applies to program-counter arithmetic. It must appear in
our reasoning; it is not the arithmetic of unbounded natural numbers.

The starter supplies `read_zero` and `write_zero`. Your first proofs will show that a write
to a nonzero register reads back the new value and preserves all other registers.

# Instructions and Programs

```anchor instructions (module := MiniRisc.Model)
inductive Instruction where
  | add (rd rs1 rs2 : Register)
  | addi (rd rs1 : Register) (immediate : BitVec 12)
  | beq (rs1 rs2 : Register) (offset : BitVec 13)
  | bne (rs1 rs2 : Register) (offset : BitVec 13)
  | ebreak
  deriving DecidableEq, Repr

inductive Fault where
  | misaligned (address : Word)
  | outsideCode (address : Word)
  | breakpoint
  deriving DecidableEq, Repr

def signed {width : Nat} (value : BitVec width) : Word :=
  BitVec.ofInt 64 value.toInt
```

`add` adds two registers; `addi` adds a signed 12-bit immediate. `beq` and `bne` branch on
equality and inequality using a signed 13-bit byte offset. The target is relative to the
current PC. Otherwise execution proceeds to `pc + 4`. `ebreak` requests a breakpoint trap.
It does not retire as a successful instruction.

`signed` converts an immediate to its signed integer interpretation, then represents that
integer as a 64-bit word. Thus a 12-bit immediate encoding minus one acts as a decrement,
rather than an addition of the unsigned number 4095.

```anchor program (module := MiniRisc.Model)
structure Program where
  base : Nat := 0
  code : Array Instruction
  deriving DecidableEq, Repr

def Program.finish (program : Program) : Nat := program.base + 4 * program.code.size

def Program.Valid (program : Program) : Prop :=
  program.base % 4 = 0 ∧ program.finish ≤ 2 ^ 64

def fetch (program : Program) (pc : Word) : Except Fault Instruction :=
  let address := pc.toNat
  if address % 4 ≠ 0 then .error (.misaligned pc)
  else if program.base ≤ address ∧ address + 4 ≤ program.finish ∧
      address + 4 ≤ 2 ^ 64 ∧ (address - program.base) % 4 = 0 then
    match program.code[(address - program.base) / 4]? with
    | some instruction => .ok instruction
    | none => .error (.outsideCode pc)
  else .error (.outsideCode pc)
```

Each array element occupies one four-byte instruction position, beginning at `base`.
`Program.Valid` describes an aligned image that does not cross the address-space boundary.
`fetch` checks the PC's alignment and whole-instruction bounds before selecting an entry.
Falling past the image is a fault, not successful completion.

The array contains decoded instructions, not binary encodings. Instruction storage is immutable
and there is no data memory yet. This lets us focus on control flow and register state before
introducing byte decoding, load/store behavior, and permissions.

# Specify Successful and Faulting Steps

The relation `Exec instruction state next` specifies successful instruction execution.
Its rules compute arithmetic results and make control-flow conditions explicit:

```anchor instructionSemantics (module := MiniRisc.Semantics)
inductive Exec : Instruction → State → State → Prop where
  | add : Exec (.add rd rs1 rs2) state
      ({ state with pc := state.pc + 4 }.writeReg rd (state.readReg rs1 + state.readReg rs2))
  | addi : Exec (.addi rd rs1 immediate) state
      ({ state with pc := state.pc + 4 }.writeReg rd (state.readReg rs1 + signed immediate))
  | beqTaken (equal : state.readReg rs1 = state.readReg rs2)
      (aligned : (state.pc + signed offset).toNat % 4 = 0) :
      Exec (.beq rs1 rs2 offset) state { state with pc := state.pc + signed offset }
  | beqNext (different : state.readReg rs1 ≠ state.readReg rs2) :
      Exec (.beq rs1 rs2 offset) state { state with pc := state.pc + 4 }
  | bneTaken (different : state.readReg rs1 ≠ state.readReg rs2)
      (aligned : (state.pc + signed offset).toNat % 4 = 0) :
      Exec (.bne rs1 rs2 offset) state { state with pc := state.pc + signed offset }
  | bneNext (equal : state.readReg rs1 = state.readReg rs2) :
      Exec (.bne rs1 rs2 offset) state { state with pc := state.pc + 4 }
```

There are separate rules for taken and untaken branches. A taken target must be four-byte
aligned. An untaken target is not checked. Register values used as operands come from the
pre-state, including when the destination register is also a source.

Faults are also part of the specification:

```anchor faultSemantics (module := MiniRisc.Semantics)
inductive ExecFault : Instruction → State → Fault → Prop where
  | breakpoint : ExecFault .ebreak state .breakpoint
  | beqMisaligned (equal : state.readReg rs1 = state.readReg rs2)
      (bad : (state.pc + signed offset).toNat % 4 ≠ 0) :
      ExecFault (.beq rs1 rs2 offset) state (.misaligned (state.pc + signed offset))
  | bneMisaligned (different : state.readReg rs1 ≠ state.readReg rs2)
      (bad : (state.pc + signed offset).toNat % 4 ≠ 0) :
      ExecFault (.bne rs1 rs2 offset) state (.misaligned (state.pc + signed offset))

inductive Faulted (program : Program) : State → Fault → Prop where
  | fetch (failed : fetch program state.pc = .error fault) : Faulted program state fault
  | execute (fetched : fetch program state.pc = .ok instruction)
      (failed : ExecFault instruction state fault) : Faulted program state fault
```

`ExecFault` specifies instruction faults. `Faulted` adds fetch failures and identifies the
instruction when fetching succeeds. No new state is returned by a fault: the runner must
retain the complete pre-instruction state. This project treats `fetch` as part of the supplied
program-image model; the relation does not independently derive byte-level instruction fetching.

The single-step and finite-execution relations connect instructions into program behavior:

```anchor executionSteps (module := MiniRisc.Semantics)
inductive Step (program : Program) : State → State → Prop where
  | instruction (fetched : fetch program state.pc = .ok instruction)
      (executed : Exec instruction state next) : Step program state next

inductive Steps (program : Program) : Nat → State → State → Prop where
  | refl : Steps program 0 state state
  | next (first : Step program state middle) (rest : Steps program count middle final) :
      Steps program (count + 1) state final
```

`Step program state next` requires both a successful fetch and a permitted instruction step.
`Steps program count state final` describes exactly `count` successful steps. Its reflexive
case performs zero steps; its inductive case adds one step before the rest of the execution.
A trap is not an extra successful step.

# Compute an Instruction Step

The executable implementation follows the specification's cases:

```anchor execute (module := MiniRisc.Model)
def execute (state : State) (instruction : Instruction) : Except Fault State :=
  let next := { state with pc := state.pc + 4 }
  match instruction with
  | .add rd rs1 rs2 =>
      .ok (next.writeReg rd (state.readReg rs1 + state.readReg rs2))
  | .addi rd rs1 immediate =>
      .ok (next.writeReg rd (state.readReg rs1 + signed immediate))
  | .beq rs1 rs2 offset =>
      if state.readReg rs1 = state.readReg rs2 then jump state (state.pc + signed offset)
      else .ok next
  | .bne rs1 rs2 offset =>
      if state.readReg rs1 ≠ state.readReg rs2 then jump state (state.pc + signed offset)
      else .ok next
  | .ebreak => .error .breakpoint

def step (program : Program) (state : State) : Except Fault State := do
  let instruction ← fetch program state.pc
  execute state instruction
```

`jump` accepts an aligned target and changes only the PC, or returns a misalignment fault.
`step` fetches before executing; calling `execute` directly bypasses fetch checks. In particular,
testing an instruction with `execute` does not show that a program can fetch it at a given PC.

Students will prove both success equivalences and fault equivalences. Proving only that
successful executions are correct would leave room for an interpreter that reports incorrect
faults instead of carrying out valid instructions.

# Specify and Implement Bounded Execution

We want a runner's result to explain both the execution that occurred and why it stopped:

```anchor runContract (module := MiniRisc.Exercises)
def RunCorrect : Prop :=
  ∀ (fuel : Nat) (program : Program) (state : State),
    let result := run fuel program state
    Steps program result.retired state result.state ∧
    (result.stop = .suspended → result.retired = fuel) ∧
    (∀ fault, result.stop = .trapped fault →
      Faulted program result.state fault ∧ result.retired < fuel)
```

If execution is suspended, every unit of fuel retired an instruction. If it traps, there is
a specified fault at the returned state, and the number of retired instructions is strictly
less than the fuel allowance. In both cases the returned state is reachable by the reported
number of successful steps.

```anchor runner (module := MiniRisc.Model)
inductive Stop where
  | suspended
  | trapped (fault : Fault)
  deriving DecidableEq, Repr

structure RunResult where
  state : State
  stop : Stop
  retired : Nat
  deriving DecidableEq, Repr

def run (fuel : Nat) (program : Program) (state : State) : RunResult :=
  match fuel with
  | 0 => ⟨state, .suspended, 0⟩
  | fuel + 1 =>
      match step program state with
      | .error fault => ⟨state, .trapped fault, 0⟩
      | .ok next =>
          let result := run fuel program next
          { result with retired := result.retired + 1 }
```

Fuel counts successfully retired instructions. Zero fuel suspends before fetching, even if
the current PC would fault. A failed attempt consumes no retired instruction and leaves the
state at the faulting PC. Exhausting fuel does not establish that the program has finished.
The saved state can be passed to another run to continue execution.

# A Countdown Program

```anchor countdown (module := MiniRisc.Countdown)
def countdown : Program := {
  code := #[
    .beq 10 0 12,
    .addi 10 10 (BitVec.ofInt 12 (-1)),
    .beq 0 0 (BitVec.ofInt 13 (-8)),
    .ebreak] }

def start (value : Word) : State := ({} : State).writeReg 10 value
```

The four instruction addresses are 0, 4, 8, and 12:

1. At 0, if register 10 is zero, branch to the breakpoint at 12.
2. At 4, decrement register 10.
3. At 8, take the always-true equality branch back to 0.
4. At 12, request a breakpoint.

The zero case exits before decrementing, which matters for unsigned arithmetic: decrementing
zero would wrap to `2^64 - 1`. Each nonzero loop iteration retires three instructions, and
the final taken exit branch retires one. Attempting the breakpoint requires one additional
unit of fuel but does not retire another instruction.

```leanInit machineProject
```

```lean machineProject
open Course.MiniRisc

example : (run 10 countdown (start 3)).stop = .suspended := by decide
example : (run 10 countdown (start 3)).state.pc = 12 := by decide
example : (run 11 countdown (start 3)).stop = .trapped .breakpoint := by decide
example : (run 11 countdown (start 3)).retired = 10 := by decide
example : (run 11 countdown (start 3)).state.readReg 10 = 0 := by decide
```

The first run reaches the exit marker but has no fuel left to observe the breakpoint.
The second run observes it. These are different outcomes, even though both runs reach a
state with a zero counter at PC 12.

# The Program-Correctness Goal

```anchor countdownContract (module := MiniRisc.Exercises)
def CountdownCorrect : Prop :=
  ∀ (state : State), state.pc = 0 →
    let input := (state.readReg 10).toNat
    let result := run (3 * input + 2) countdown state
    result.stop = .trapped .breakpoint ∧
    result.state.pc = 12 ∧ result.state.readReg 10 = 0 ∧
    result.retired = 3 * input + 1 ∧
    (∀ register : Register, register ≠ 10 → result.state.readReg register = state.readReg register)
```

The theorem ranges over arbitrary initial register files with PC zero, not just `start`.
It specifies the stop reason, final PC, result, exact number of retired instructions, and
preservation of every other architectural register. An immediate trap, a zero-fuel suspension,
or an interpreter that simply clears the counter would not satisfy it.

To prove it, reason about executions beginning at the loop header. An iteration with a
positive counter returns to the header with its unsigned value decreased by one. The zero
case reaches the exit marker without another decrement. Induction on the unsigned counter
value supplies both the result and the finite execution bound.

The starter supplies an arithmetic bridge in `Course.MiniRisc.Support`:

```anchor decrement (module := MiniRisc.Support)
theorem decrement_toNat (value : Word) (positive : 0 < value.toNat) :
    (value - 1).toNat = value.toNat - 1 := by
  have enough : (1 : Word) ≤ value := by
    change 1 ≤ value.toNat
    omega
  simpa using BitVec.toNat_sub_of_le enough
```

Use it after establishing that the counter is positive. You will also need to relate adding
the sign-extended minus-one immediate to subtracting one. Explain why the positivity
hypothesis is essential. A bitvector alone is not a decreasing natural-number measure.

# Core Assignment

1. *Register behavior.* Prove `Exercises.RegisterLaws`. Include aliasing of source and
   destination registers when reasoning about arithmetic instructions.
2. *Instruction conformance.* Prove `Exercises.ExecuteCorrect` and
   `Exercises.ExecuteFaultCorrect`. Treat taken and untaken branches separately.
3. *Whole-step conformance.* Prove `Exercises.StepCorrect` and `Exercises.StepFaultCorrect`,
   connecting fetch and instruction execution to `Step` and `Faulted`.
4. *Executions and stopping.* Prove `Exercises.RunCorrect` by induction on fuel. Explain
   why zero fuel does not imply that the next instruction is safe, and why a trapped
   instruction is absent from the successful-step count.
5. *A loop with a result.* Prove `Exercises.CountdownCorrect`. First establish a theorem
   for one nonzero iteration and a theorem for the zero case. Use an invariant at the loop
   header and an induction on the counter's unsigned value. Include the register-frame
   guarantee and account for the final breakpoint attempt.

Create `MiniRisc/Solution.lean`, import `MiniRisc.Exercises` and `MiniRisc.Support`, and import
your solution from `Checks.lean`. Keep the supplied definitions and exercise propositions
fixed. Audit your theorem dependencies using `#print axioms`, as demonstrated in `Audit.lean`.
Do not discharge obligations with new axioms or proof placeholders.

Submit the proofs with an explanation of the loop invariant, decreasing measure, fuel bound,
and trusted model. Include a trace for a small input and an explanation of why suspension
and trapping are different. Use an agent to explore proofs one lemma at a time; require it
to state which PC and counter relationships its induction hypothesis preserves.

# Optional Extensions

1. Prove `Exercises.Resumption`: splitting a run at a suspension point agrees with one
   longer run, including the total number of retired instructions. Explain why the hypothesis
   says the first run suspended rather than trapped.
2. Replace the loop's conditional structure with a `bne`-based version. Specify its new
   instruction count and prove that it computes the same counter result with the same frame.
3. Relocate the program to an aligned nonzero base. State and prove the bounds needed to
   connect the relocated execution to the original. Do not assume PC addition cannot wrap.

# What the Model Does and Does Not Establish

This project models sequential register operations and control flow. It does not model
data memory, binary decoding, interrupts, privilege modes, or hardware trap handling.
Arithmetic wraps at 64 bits; taken branch targets and fetch addresses require four-byte
alignment. These are deliberate instruction-level conventions, not a proof of agreement
with a physical processor.

The runner always terminates because its fuel decreases. That fact does not establish
termination of the simulated program. The countdown proof must show that a sufficient bound
reaches the specified exit, without an earlier fault. This distinction between a terminating
interpreter and a terminating guest program is central to the project.
