import ProtectedMemory.Semantics

namespace Course.ProtectedMemory.Exercises

-- These propositions are student obligations, not assumed theorems.

def CheckCorrect : Prop :=
  ∀ (memory : Memory) (domain : Domain) (access : Access) (address : Word)
    (result : Except Fault Nat), check memory domain access address = result ↔
      CheckSpec memory domain access address result

def ReadCorrect : Prop :=
  ∀ (memory : Memory) (offset : Nat), offset + width ≤ memory.bytes.size →
    Loaded memory offset (readWord memory.bytes offset)

def WriteCorrect : Prop :=
  ∀ (memory : Memory) (offset : Nat) (value : Word), offset + width ≤ memory.bytes.size →
    Stored memory { memory with bytes := writeWord memory.bytes offset value } offset value

def OperateCorrect : Prop :=
  ∀ (memory after : Memory) (domain : Domain) (command : Command) (reply : Reply),
    operate memory domain command = (reply, after) ↔ Step domain memory command reply after

def FailureAtomicity : Prop :=
  ∀ (memory after : Memory) (domain : Domain) (command : Command) (reason : Fault),
    operate memory domain command = (.fault reason, after) → after = memory

def StepPreservation : Prop :=
  ∀ (before after : Memory) (domain : Domain) (command : Command) (reply : Reply),
    before.Valid → Step domain before command reply after → after.Valid

def LayoutPreservation : Prop :=
  ∀ (memory : Memory) (domain : Domain) (command : Command),
    SameLayout memory (operate memory domain command).2

def Preservation : Prop :=
  ∀ (memory : Memory) (domain : Domain) (command : Command), memory.Valid →
    (operate memory domain command).2.Valid

def StoreFrame : Prop :=
  ∀ (before after : Memory) (domain : Domain) (address value : Word),
    operate before domain (.store address value) = (.stored, after) →
      SameLayout before after ∧
      ∀ other : Nat, other < address.toNat ∨ address.toNat + width ≤ other →
        byteAt after other = byteAt before other

def LoadAfterStore : Prop :=
  ∀ (memory : Memory) (domain : Domain) (address value : Word) (offset : Nat),
    check memory domain .write address = .ok offset →
    check memory domain .read address = .ok offset →
    let after := (operate memory domain (.store address value)).2
    operate after domain (.load address) = (.loaded value, after)

-- ANCHOR: isolationGoals
def StepIsolation : Prop :=
  ∀ (before after : Memory) (actor owner : Domain) (command : Command) (reply : Reply),
    before.Valid → actor ≠ owner → Step actor before command reply after →
    ∀ address : Nat, Owned before owner address → byteAt after address = byteAt before address

def TraceIsolation : Prop :=
  ∀ (memory : Memory) (actor owner : Domain) (commands : List Command),
    memory.Valid → actor ≠ owner →
    ∀ address : Nat, Owned memory owner address →
      byteAt (runTrace memory actor commands).2 address = byteAt memory address
-- ANCHOR_END: isolationGoals

def TraceCorrect : Prop :=
  ∀ (before after : Memory) (domain : Domain) (commands : List Command) (replies : List Reply),
    runTrace before domain commands = (replies, after) ↔ Trace domain before commands replies after

-- ANCHOR: confidentialityGoal
def VisibleEqual (domain : Domain) (left right : Memory) : Prop :=
  SameLayout left right ∧
    ∀ address : Nat, Owned left domain address → byteAt left address = byteAt right address

def RepliesIndependent : Prop :=
  ∀ (left right : Memory) (domain : Domain) (commands : List Command),
    left.Valid → right.Valid → VisibleEqual domain left right →
      (runTrace left domain commands).1 = (runTrace right domain commands).1
-- ANCHOR_END: confidentialityGoal

end Course.ProtectedMemory.Exercises
