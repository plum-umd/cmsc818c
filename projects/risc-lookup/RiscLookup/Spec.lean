import Plos.RiscV.Call
import Plos.RiscV.Code

namespace Course.RiscLookup

open Plos.RiscV

-- ANCHOR: table
/-- A nonwrapping sequence of readable 64-bit cells, with all word values allowed. -/
def Table (memory : Memory) (mode : Mode) (address : Word) (channels : List Word) : Prop :=
  address.toNat + 8 * channels.length ≤ 2^64 ∧
    ∀ index channel, channels[index]? = some channel →
      memory.load mode .read (address + BitVec.ofNat 64 (8 * index)) .double = .ok channel.toNat
-- ANCHOR_END: table

-- ANCHOR: result
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
-- ANCHOR_END: result

-- ANCHOR: returnMarker
/-- The harness must not mistake an instruction within the image for a completed call. -/
structure ReturnAt (base returnAddress : Word) (code : Array InstructionWord) : Prop where
  aligned : returnAddress.toNat % 4 = 0
  distinct : base ≠ returnAddress
  outside : returnAddress.toNat < base.toNat ∨
    base.toNat + 4 * code.size ≤ returnAddress.toNat
-- ANCHOR_END: returnMarker

-- ANCHOR: inputs
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
-- ANCHOR_END: inputs

end Course.RiscLookup
