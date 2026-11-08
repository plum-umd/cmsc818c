import Std

namespace Course.MiniRisc

-- ANCHOR: machineState
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
-- ANCHOR_END: machineState

-- ANCHOR: instructions
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
-- ANCHOR_END: instructions

-- ANCHOR: program
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
-- ANCHOR_END: program

def jump (state : State) (target : Word) : Except Fault State :=
  if target.toNat % 4 = 0 then .ok { state with pc := target }
  else .error (.misaligned target)

-- ANCHOR: execute
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
-- ANCHOR_END: execute

-- ANCHOR: runner
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
-- ANCHOR_END: runner

@[simp] theorem read_zero (state : State) : state.readReg 0 = 0 := rfl

@[simp] theorem write_zero (state : State) (value : Word) : state.writeReg 0 value = state := rfl

@[simp] theorem run_zero (program : Program) (state : State) :
    run 0 program state = ⟨state, .suspended, 0⟩ := rfl

end Course.MiniRisc
