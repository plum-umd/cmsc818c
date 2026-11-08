import MiniRisc.Semantics
import MiniRisc.Countdown

namespace Course.MiniRisc.Exercises

-- Specifications for student proofs, not assumed theorems.

def RegisterLaws : Prop :=
  (∀ (state : State) (rd : Register) (value : Word), rd.val ≠ 0 →
    (state.writeReg rd value).readReg rd = value) ∧
  (∀ (state : State) (rd other : Register) (value : Word), other ≠ rd →
    (state.writeReg rd value).readReg other = state.readReg other)

def ExecuteCorrect : Prop :=
  ∀ (state next : State) (instruction : Instruction),
    execute state instruction = .ok next ↔ Exec instruction state next

def ExecuteFaultCorrect : Prop :=
  ∀ (state : State) (instruction : Instruction) (fault : Fault),
    execute state instruction = .error fault ↔ ExecFault instruction state fault

def StepCorrect : Prop :=
  ∀ (program : Program) (state next : State),
    step program state = .ok next ↔ Step program state next

def StepFaultCorrect : Prop :=
  ∀ (program : Program) (state : State) (fault : Fault),
    step program state = .error fault ↔ Faulted program state fault

-- ANCHOR: runContract
def RunCorrect : Prop :=
  ∀ (fuel : Nat) (program : Program) (state : State),
    let result := run fuel program state
    Steps program result.retired state result.state ∧
    (result.stop = .suspended → result.retired = fuel) ∧
    (∀ fault, result.stop = .trapped fault →
      Faulted program result.state fault ∧ result.retired < fuel)
-- ANCHOR_END: runContract

def Resumption : Prop :=
  ∀ (firstFuel secondFuel : Nat) (program : Program) (state : State),
    let first := run firstFuel program state
    let second := run secondFuel program first.state
    first.stop = .suspended →
      run (firstFuel + secondFuel) program state =
        { second with retired := first.retired + second.retired }

-- ANCHOR: countdownContract
def CountdownCorrect : Prop :=
  ∀ (state : State), state.pc = 0 →
    let input := (state.readReg 10).toNat
    let result := run (3 * input + 2) countdown state
    result.stop = .trapped .breakpoint ∧
    result.state.pc = 12 ∧ result.state.readReg 10 = 0 ∧
    result.retired = 3 * input + 1 ∧
    (∀ register : Register, register ≠ 10 → result.state.readReg register = state.readReg register)
-- ANCHOR_END: countdownContract

end Course.MiniRisc.Exercises
