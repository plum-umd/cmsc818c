import RiscHandles.Native

namespace Course.RiscHandles.Exercises

open Plos.RiscV

-- ANCHOR: tableAppend
/-- Derive the extended representation from the byte-level effect, independently of assembly. -/
def TableAppend : Prop :=
  ∀ (before after : Memory) (mode : Mode) (address channel : Word)
    (channels : List Word) (capacity : Nat),
    Buffer before mode address channels capacity → channels.length < capacity →
    Store64Effect before after (address + BitVec.ofNat 64 (8 * channels.length)) channel →
      Lookup.Table after mode address (channels ++ [channel])
-- ANCHOR_END: tableAppend

-- ANCHOR: runCorrect
def RunCorrect : Prop :=
  ∀ (state : State) (base ret : Word) (channels : List Word) (capacity fuel : Nat),
    Inputs code state base ret channels capacity → 16 ≤ fuel →
      Correct channels capacity (state.readReg 10) (state.readReg 13) ret state
        (resumeCall ret fuel state)
-- ANCHOR_END: runCorrect

def CallCorrect : Prop :=
  ∀ (call : Call) (original prepared : State) (channels : List Word) (capacity fuel : Nat),
    call.prepare original = .ok prepared →
    Inputs code prepared call.entry call.returnAddress channels capacity → 16 ≤ fuel →
      ∃ result, callRoutine call fuel original = .ok result ∧
        Correct channels capacity (prepared.readReg 10) (prepared.readReg 13)
          call.returnAddress prepared result

-- ANCHOR: nativeAppend
/-- Preserve the persistent invariant while taking memory and length from encoded execution. -/
def NativeAppendCorrect : Prop :=
  ∀ (table : Native) (channel : Word), table.Valid →
    let result := table.appendResult channel
    let after := table.append channel
    result.stop = .returned ∧ after.Valid ∧
      after.memory = result.state.memory ∧
      after.length = (result.state.readReg 10).toNat ∧ after.capacity = table.capacity ∧
      if table.length < table.capacity then
        result.state.readReg 11 = 1 ∧ after.words = table.words ++ [channel] ∧
        Store64Effect table.memory after.memory
          (256 + BitVec.ofNat 64 (8 * table.length)) channel
      else result.state.readReg 11 = 0 ∧ after = table
-- ANCHOR_END: nativeAppend

-- ANCHOR: nativeLookup
def NativeLookupCorrect : Prop :=
  ∀ (table : Native) (index : Nat), table.Valid → index < 2^64 →
    Lookup.Correct table.words index (table.lookupPrepared index) (table.lookupResult index)

/-- The new cell can be read by the independently verified lookup without rebuilding an image. -/
def AppendThenLookup : Prop :=
  ∀ (table : Native) (channel : Word), table.Valid → table.length < table.capacity →
    let after := table.append channel
    let result := after.lookupResult table.length
    result.stop = .returned ∧ result.state.readReg 10 = channel ∧ result.state.readReg 11 = 1
-- ANCHOR_END: nativeLookup

end Course.RiscHandles.Exercises
