import RiscHandles

namespace Course.RiscHandles.Fixtures

open Plos.RiscV

def sameState (left right : State) : Bool :=
  decide (left.pc = right.pc ∧ left.memory = right.memory ∧ left.mode = right.mode) &&
    (List.finRange 32).all fun r => decide (left.readReg r = right.readReg r)

/-- Independent expected memory for the success case; a full buffer has no memory effect. -/
def expectedMemory (before : Memory) (length capacity : Nat) (address channel : Word) :
    Option Memory :=
  if length < capacity then
    (before.store64 .user (address + BitVec.ofNat 64 (8*length)) channel).toOption
  else some before

def routineCall (base ret address : Word) (length capacity : Nat) (channel : Word) : Call := {
  entry := base, returnAddress := ret, stackPointer := 0
  arguments := fun i => if i.val = 0 then address
    else if i.val = 1 then BitVec.ofNat 64 length
    else if i.val = 2 then BitVec.ofNat 64 capacity
    else if i.val = 3 then channel else 0 }

def checkResult (prepared : State) (ret address channel : Word) (length capacity : Nat)
    (result : CallResult) : Bool :=
  decide (result.stop = .returned ∧ result.state.pc = ret ∧ result.retired ≤ 16 ∧
    result.state.mode = prepared.mode ∧
    result.state.readReg 10 = BitVec.ofNat 64 (if length < capacity then length+1 else length) ∧
    result.state.readReg 11 = (if length < capacity then 1 else 0)) &&
    decide (some result.state.memory =
      expectedMemory prepared.memory length capacity address channel) &&
    (List.finRange 32).all fun r =>
      if r = 10 ∨ r = 11 ∨ r = 14 then true
      else decide (result.state.readReg r = prepared.readReg r)

def checkSlices (prepared : State) (ret : Word) : Bool :=
  let whole := resumeCall ret 16 prepared
  decide (whole.stop = .returned) && (List.range 17).all fun fuel =>
    let first := resumeCall ret fuel prepared
    let rest := resumeCall ret (16-fuel) first.state
    decide (rest.stop = .returned ∧ first.retired + rest.retired = whole.retired) &&
      sameState rest.state whole.state

/-- Check a relocated image using separate executable code and writable data mappings. -/
def checkRoutineCase (image : Array InstructionWord) (base : Nat)
    (channels : List Word) (capacity : Nat) (channel : Word) : Bool := Id.run do
  if image.size > 16 ∨ channels.length > capacity then return false
  let data := (Image.memory #[] channels capacity).bytes.extract 256 (256 + 8*capacity)
  let original : State := {
    registers := Vector.ofFn fun r => BitVec.ofNat 64 (1000+r.val)
    memory := {
      bytes := Array.replicate base 0 ++ Assembler.bytes image ++
        Array.replicate (1024-(base+4*image.size)) 0 ++ data
      regions := [⟨base, 4*image.size, true, false, true, true⟩,
        ⟨1024, 8*capacity, true, true, false, true⟩] } }
  let ret := BitVec.ofNat 64 (base+4*image.size+4)
  let call := routineCall (BitVec.ofNat 64 base) ret 1024 channels.length capacity channel
  let .ok prepared := call.prepare original | return false
  return checkResult prepared ret 1024 channel channels.length capacity
    (resumeCall ret 16 prepared) && checkSlices prepared ret

/-- Full and overfull calls must not touch an unreadable, misaligned data address. -/
def checkFull (image : Array InstructionWord) (length capacity : Nat) : Bool := Id.run do
  let original : State := { memory := {
    bytes := Assembler.bytes image
    regions := [⟨0, 4*image.size, true, false, true, true⟩] } }
  let ret := BitVec.ofNat 64 (4*image.size+4)
  let call := routineCall 0 ret 1026 length capacity 42
  let .ok prepared := call.prepare original | return false
  return checkResult prepared ret 1026 42 length capacity (resumeCall ret 16 prepared)

def checkRoutine (image : Array InstructionWord) : Bool :=
  [0, 256].all (fun base =>
    [([], 0), ([], 3), ([0], 1), ([7, 0], 4), ([7, 7], 3)].all fun (channels, capacity) =>
      ([0, 42, BitVec.ofNat 64 (2^64-1)] : List Word).all fun channel =>
        checkRoutineCase image base channels capacity channel) &&
    checkFull image 0 0 && checkFull image 3 2

-- ANCHOR: persistenceChecks
/-- Fill one retained image, look up every result, and then refuse another append. -/
def checkPersistent (image : Array InstructionWord) (update : Native → Word → Native) : Bool :=
    Id.run do
  let mut table : Native := ⟨Image.memory image [7] 4, 1, 4⟩
  let mut logical : List Word := [7]
  for channel in ([0, 7, BitVec.ofNat 64 (2^64-1)] : List Word) do
    let result := table.appendResult channel
    let next := update table channel
    if result.stop ≠ .returned ∨ next.memory ≠ result.state.memory ∨
        next.length ≠ (result.state.readReg 10).toNat ∨ next.capacity ≠ table.capacity then
      return false
    logical := logical ++ [channel]
    if next.words ≠ logical then return false
    table := next
    for index in List.range logical.length do
      let found := table.lookupResult index
      if found.stop ≠ .returned ∨ found.state.readReg 10 ≠ logical[index]! ∨
          found.state.readReg 11 ≠ 1 then return false
  let refused := update table 99
  let result := table.appendResult 99
  return decide (refused = table ∧ result.stop = .returned ∧ result.state.readReg 11 = 0 ∧
    refused.memory = result.state.memory ∧ refused.length = (result.state.readReg 10).toNat)

def candidateChecks : Bool := checkRoutine code && checkPersistent code Native.append
-- ANCHOR_END: persistenceChecks

end Course.RiscHandles.Fixtures
