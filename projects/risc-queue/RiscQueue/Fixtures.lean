import RiscQueue

namespace Course.RiscQueue.Fixtures

open Plos.RiscV

def sameState (left right : State) : Bool :=
  decide (left.pc = right.pc ∧ left.memory = right.memory ∧ left.mode = right.mode) &&
    (List.finRange 32).all fun r => decide (left.readReg r = right.readReg r)

def routineCall (base ret address : Word) (head count capacity : Nat) : Call := {
  entry := base, returnAddress := ret, stackPointer := 0
  arguments := fun i => if i.val = 0 then address
    else if i.val = 1 then BitVec.ofNat 64 head
    else if i.val = 2 then BitVec.ofNat 64 count
    else if i.val = 3 then BitVec.ofNat 64 capacity else 0 }

def checkResult (before : State) (ret value : Word) (head count capacity : Nat)
    (result : CallResult) : Bool :=
  decide (result.stop = .returned ∧ result.state.pc = ret ∧ result.retired ≤ 16 ∧
    result.state.memory = before.memory ∧ result.state.mode = before.mode ∧
    result.state.readReg 10 = (if count = 0 then 0 else value) ∧
    (result.state.readReg 11).toNat = (if count = 0 then head else nextHead head capacity) ∧
    (result.state.readReg 12).toNat = count-1 ∧
    result.state.readReg 13 = (if count = 0 then 0 else 1)) &&
    (List.finRange 32).all fun r =>
      if r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 then true
      else decide (result.state.readReg r = before.readReg r)

def checkSlices (prepared : State) (ret : Word) : Bool :=
  let whole := resumeCall ret 16 prepared
  decide (whole.stop = .returned) && (List.range 17).all fun fuel =>
    let first := resumeCall ret fuel prepared
    let rest := resumeCall ret (16-fuel) first.state
    decide (rest.stop = .returned ∧ first.retired + rest.retired = whole.retired) &&
      sameState rest.state whole.state

def checkRoutineCase (image : Array InstructionWord) (base : Nat) (cells : List Word)
    (head count : Nat) (readable : Bool := true) : Bool := Id.run do
  if image.size > 24 ∨ head ≥ cells.length ∨ count > cells.length then return false
  let data := (Image.memory #[] cells cells.length).bytes.extract 256 (256+8*cells.length)
  let original : State := {
    registers := Vector.ofFn fun r => BitVec.ofNat 64 (1000+r.val)
    memory := {
      bytes := Array.replicate base 0 ++ Assembler.bytes image ++
        Array.replicate (1024-(base+4*image.size)) 0 ++ data
      regions := [⟨base, 4*image.size, true, false, true, true⟩,
        ⟨1024, 8*cells.length, readable, false, false, true⟩] } }
  let ret := BitVec.ofNat 64 (base+4*image.size+4)
  let address : Word := if readable then 1024 else 1026
  let call := routineCall (BitVec.ofNat 64 base) ret address head count cells.length
  let .ok prepared := call.prepare original | return false
  return checkResult prepared ret cells[head]! head count cells.length
    (resumeCall ret 16 prepared) && checkSlices prepared ret

def checkRoutine (image : Array InstructionWord) : Bool :=
  [0, 512].all fun base =>
    ([([0], 0, 0), ([0], 0, 1), ([10, 20, 30, 40], 3, 4),
      ([10, 20, 30, 40], 0, 4), ([10, 20, 30, 40], 3, 1),
      ([BitVec.ofNat 64 (2^64-1), 0], 0, 2)] : List (List Word × Nat × Nat)).all
      (fun (cells, head, count) => checkRoutineCase image base cells head count) &&
      checkRoutineCase image base [7] 0 0 false

-- ANCHOR: ringChecks
/-- Check wrapped storage, reuse of popped slots, full state, and repeated emptying. -/
def checkRing (image : Array InstructionWord) (pop : Ring → Word × Ring)
    (push : Ring → Word → Ring) : Bool := Id.run do
  let mut ring : Ring := ⟨Image.memory image [10, 20, 30, 40] 4, 4, 3, 2⟩
  let mut logical : List Word := [40, 10]
  let before := ring
  let result := ring.popResult
  let (value, after) := pop ring
  if result.stop ≠ .returned ∨ value ≠ 40 ∨ value ≠ result.state.readReg 10 ∨
      after.memory ≠ ring.memory ∨ after.head ≠ (result.state.readReg 11).toNat ∨
      after.count ≠ (result.state.readReg 12).toNat ∨ after.capacity ≠ 4 then return false
  ring := after
  logical := logical.tail
  for value in ([0, BitVec.ofNat 64 (2^64-1), 10] : List Word) do
    let index := View.slot ring.head ring.capacity ring.count
    let write := ring.writeResult index value
    let next := push ring value
    if write.stop ≠ .returned ∨ next.memory ≠ write.state.memory ∨
        next.head ≠ ring.head ∨ next.count ≠ ring.count+1 ∨
        next.capacity ≠ ring.capacity then
      return false
    if next.cells ≠ ring.cells.set index value then return false
    logical := logical ++ [value]
    if next.words ≠ logical then return false
    ring := next
  for expected in logical do
    let result := ring.popResult
    let (value, next) := pop ring
    if value ≠ expected ∨ value ≠ result.state.readReg 10 ∨ result.stop ≠ .returned ∨
        next.memory ≠ ring.memory ∨ next.head ≠ (result.state.readReg 11).toNat ∨
        next.count ≠ (result.state.readReg 12).toNat ∨ next.capacity ≠ ring.capacity then
      return false
    ring := next
  return decide (ring.count = 0 ∧ ring.words = [] ∧ before.words = [40, 10])

def candidateChecks : Bool := checkRoutine code && checkRing code Ring.pop Ring.push
-- ANCHOR_END: ringChecks

/-- Run after constructing the actual correctness bundle; proof arguments are erased at runtime. -/
def policyChecks (correct : CorrectRing) : Bool := Id.run do
  let mut queue := Policy.fromList [1, 2, 1]
  let full : Policy.Queue := .native (Ring.init [1, 2] 2)
    (Ring.init_valid _ _ (by decide) (by decide) (by decide))
  let sameFull := Policy.enqueue correct full 2
  match full, sameFull with
  | .native before _, .native after _ => if before ≠ after then return false
  | _, _ => return false
  let duplicate := Policy.enqueue correct queue 1
  if Policy.view duplicate ≠ [1, 2, 1] then return false
  let removed := Policy.remove duplicate 1
  if Policy.view removed ≠ [2] then return false
  queue := Policy.fromList []
  for pid in List.range 12 do queue := Policy.enqueue correct queue pid
  if Policy.view queue ≠ List.range 12 then return false
  for pid in List.range 12 do
    let some (actual, rest) := Policy.dequeue correct queue | return false
    if actual ≠ pid then return false
    queue := rest
  if !Policy.isEmpty queue then return false
  let huge := 2^64+3
  queue := Policy.enqueue correct queue huge
  if Policy.view queue ≠ [huge] then return false
  let some (actual, rest) := Policy.dequeue correct queue | return false
  return decide (actual = huge ∧ Policy.view rest = [])

end Course.RiscQueue.Fixtures
