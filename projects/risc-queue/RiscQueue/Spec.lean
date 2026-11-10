import Plos.RiscV.Append
import Plos.RiscV.TableUpdate

namespace Course.RiscQueue

open Plos.RiscV

-- ANCHOR: nextHead
def nextHead (head capacity : Nat) : Nat :=
  if head + 1 < capacity then head + 1 else 0
-- ANCHOR_END: nextHead

-- ANCHOR: correct
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
-- ANCHOR_END: correct

structure ReturnAt (base ret : Word) (code : Array InstructionWord) : Prop where
  aligned : ret.toNat % 4 = 0
  distinct : base ≠ ret
  outside : ret.toNat < base.toNat ∨ base.toNat + 4 * code.size ≤ ret.toNat

-- ANCHOR: inputs
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
-- ANCHOR_END: inputs

end Course.RiscQueue
