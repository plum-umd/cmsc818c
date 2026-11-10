import Plos.RiscV.Lookup
import Plos.RiscV.Memory

namespace Course.RiscHandles

open Plos.RiscV

-- ANCHOR: buffer
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
-- ANCHOR_END: buffer

-- ANCHOR: correct
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
-- ANCHOR_END: correct

structure ReturnAt (base ret : Word) (code : Array InstructionWord) : Prop where
  aligned : ret.toNat % 4 = 0
  distinct : base ≠ ret
  outside : ret.toNat < base.toNat ∨ base.toNat + 4 * code.size ≤ ret.toNat

-- ANCHOR: inputs
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
-- ANCHOR_END: inputs

end Course.RiscHandles
