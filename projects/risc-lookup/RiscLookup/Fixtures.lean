import RiscLookup

namespace Course.RiscLookup.Fixtures

open Plos.RiscV

/-- Encode table cells independently of the student's assembly. -/
def dataBytes (channels : List Word) : Array UInt8 :=
  (channels.flatMap fun word =>
    (List.range 8).map fun i => UInt8.ofNat (word.toNat / 2^(8*i))).toArray

-- ANCHOR: fixture
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
-- ANCHOR_END: fixture

def sameState (left right : State) : Bool :=
  decide (left.pc = right.pc ∧ left.memory = right.memory ∧ left.mode = right.mode) &&
    (List.finRange 32).all fun r => decide (left.readReg r = right.readReg r)

def checkCase (image : Array InstructionWord) (base : Nat) (channels : List Word) (index : Nat)
    (readable : Bool := true) : Bool := Id.run do
  if image.size > 128 then return false
  let call := invocation image base channels.length index
  let .ok prepared := call.prepare (initial image base channels readable) | return false
  let result := resumeCall call.returnAddress 16 prepared
  let expected := match channels[index]? with
    | none => decide (result.state.readReg 10 = 0 ∧ result.state.readReg 11 = 0)
    | some word => decide (result.state.readReg 10 = word ∧ result.state.readReg 11 = 1)
  return expected && decide (result.stop = .returned ∧ result.state.pc = call.returnAddress ∧
    result.retired ≤ 16 ∧ result.state.memory = prepared.memory ∧
    result.state.mode = prepared.mode) &&
    (List.finRange 32).all (fun r =>
      if r = 10 ∨ r = 11 ∨ r = 12 then true
      else decide (result.state.readReg r = prepared.readReg r))

/-- Every possible suspension boundary agrees with an uninterrupted successful call. -/
def checkSlices (image : Array InstructionWord) (base : Nat) (channels : List Word)
    (index : Nat) : Bool := Id.run do
  let call := invocation image base channels.length index
  let .ok prepared := call.prepare (initial image base channels) | return false
  let whole := resumeCall call.returnAddress 16 prepared
  return decide (whole.stop = .returned) && (List.range 17).all fun fuel =>
    let first := resumeCall call.returnAddress fuel prepared
    let rest := resumeCall call.returnAddress (16 - fuel) first.state
    decide (rest.stop = .returned ∧ first.retired + rest.retired = whole.retired) &&
      sameState rest.state whole.state

-- ANCHOR: candidateChecks
/-- These checks are expected to fail until the assembly body has been implemented. -/
def checkProgram (image : Array InstructionWord) : Bool :=
  let tables : List (List Word) := [[], [0], [7, 0, 42],
    [BitVec.ofNat 64 (2^63), BitVec.ofNat 64 (2^64 - 1)]]
  [0, 256].all (fun base => tables.all fun channels =>
    ((List.range (channels.length + 2)) ++ [2^64 - 1]).all fun index =>
      checkCase image base channels index && checkSlices image base channels index) &&
    checkCase image 0 [7] 1 false && checkCase image 256 [] 0 false

def candidateChecks : Bool := checkProgram code
-- ANCHOR_END: candidateChecks

end Course.RiscLookup.Fixtures
