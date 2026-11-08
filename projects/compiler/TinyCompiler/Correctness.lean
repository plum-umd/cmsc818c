import TinyCompiler.Compile

namespace Course.TinyCompiler.Exercises

open Course.MiniRisc

-- These propositions are student obligations, not supplied proofs.

def SourceComplete : Prop :=
  ∀ (statement : Stmt) (before after : Store), Eval statement before after →
    eval statement before = after

def RegisterMapping : Prop :=
  (∀ v : Variable, reg v ≠ 0 ∧ reg v ≠ 31) ∧
  (∀ left right : Variable, reg left = reg right → left = right)

def LayoutSafe : Prop :=
  ∀ statement : Stmt, (emit statement).length ≤ maxInstructions → SafeBranches statement

def Placement : Prop :=
  ∀ (base : Nat) (statement : Stmt) (program : Program), compile base statement = .ok program →
    program.Valid ∧ CodeAt (emit statement) base program ∧ SafeBranches statement ∧
      fetch program (BitVec.ofNat 64 (base + 4 * (emit statement).length)) = .ok .ebreak

-- ANCHOR: localCorrectness
def LocalCorrect : Prop :=
  ∀ (statement : Stmt) (store : Store) (machine : State) (program : Program) (address : Nat),
    SafeBranches statement → CodeAt (emit statement) address program →
    machine.pc = BitVec.ofNat 64 address → Rep store machine →
      ∃ steps : Nat, steps ≤ (emit statement).length ∧
        let result := run steps program machine
        result.stop = .suspended ∧ result.retired = steps ∧
        result.state.pc = BitVec.ofNat 64 (address + 4 * (emit statement).length) ∧
        Rep (eval statement store) result.state ∧ Frame statement machine result.state
-- ANCHOR_END: localCorrectness

-- ANCHOR: compilerCorrectness
def CompilerCorrect : Prop :=
  ∀ (base : Nat) (statement : Stmt) (program : Program) (store : Store) (machine : State),
    compile base statement = .ok program →
    machine.pc = BitVec.ofNat 64 base → Rep store machine →
      let result := run ((emit statement).length + 1) program machine
      result.stop = .trapped .breakpoint ∧
      result.state.pc = BitVec.ofNat 64 (base + 4 * (emit statement).length) ∧
      result.retired ≤ (emit statement).length ∧
      Rep (eval statement store) result.state ∧ Frame statement machine result.state
-- ANCHOR_END: compilerCorrectness

end Course.TinyCompiler.Exercises
