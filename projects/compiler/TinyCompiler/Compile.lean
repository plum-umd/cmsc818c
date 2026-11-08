import TinyCompiler.Source

namespace Course.TinyCompiler

open Course.MiniRisc

-- ANCHOR: registerMapping
def reg (v : Variable) : Register := ⟨v.val + 1, by omega⟩

def Rep (store : Store) (machine : State) : Prop :=
  ∀ v, machine.readReg (reg v) = store.read v
-- ANCHOR_END: registerMapping

-- ANCHOR: emitter
def emitExpr (destination : Variable) (expression : Expr) : Instruction :=
  match expression with
  | .var v => .add (reg destination) (reg v) 0
  | .literal value => .addi (reg destination) 0 value
  | .add left right => .add (reg destination) (reg left) (reg right)

def emit (statement : Stmt) : List Instruction :=
  match statement with
  | .skip => []
  | .assign destination expression => [emitExpr destination expression]
  | .seq first second => emit first ++ emit second
  | .ifzero test yes no =>
      let yesCode := emit yes
      let noCode := emit no
      [.bne (reg test) 0 (BitVec.ofNat 13 (4 * (yesCode.length + 2)))] ++
        yesCode ++ [.beq 0 0 (BitVec.ofNat 13 (4 * (noCode.length + 1)))] ++ noCode
-- ANCHOR_END: emitter

-- ANCHOR: checkedCompilation
def maxInstructions : Nat := 1023

inductive CompileError where
  | codeTooLarge
  | misalignedBase
  | addressOverflow
  deriving DecidableEq, Repr

def compile (base : Nat) (statement : Stmt) : Except CompileError Program :=
  let code := emit statement
  if code.length > maxInstructions then .error .codeTooLarge
  else if base % 4 ≠ 0 then .error .misalignedBase
  else if base + 4 * (code.length + 1) > 2 ^ 64 then .error .addressOverflow
  else .ok ⟨base, (code ++ [Instruction.ebreak]).toArray⟩
-- ANCHOR_END: checkedCompilation

-- ANCHOR: codeLayout
def SafeBranches : Stmt → Prop
  | .skip | .assign .. => True
  | .seq first second => SafeBranches first ∧ SafeBranches second
  | .ifzero _ yes no =>
      4 * ((emit yes).length + 2) < 2 ^ 12 ∧
      4 * ((emit no).length + 1) < 2 ^ 12 ∧ SafeBranches yes ∧ SafeBranches no

def CodeAt (code : List Instruction) (address : Nat) (program : Program) : Prop :=
  address % 4 = 0 ∧ address + 4 * code.length < 2 ^ 64 ∧
    ∀ (index : Nat) (inside : index < code.length),
      fetch program (BitVec.ofNat 64 (address + 4 * index)) = .ok code[index]
-- ANCHOR_END: codeLayout

def writes : Stmt → List Register
  | .skip => []
  | .assign v _ => [reg v]
  | .seq first second => writes first ++ writes second
  | .ifzero _ yes no => writes yes ++ writes no

def Frame (statement : Stmt) (before after : State) : Prop :=
  ∀ register, register ∉ writes statement → after.readReg register = before.readReg register

end Course.TinyCompiler
