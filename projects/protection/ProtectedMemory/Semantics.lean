import ProtectedMemory.Model

namespace Course.ProtectedMemory

-- ANCHOR: checkSemantics
inductive CheckSpec (memory : Memory) (domain : Domain) (access : Access) (address : Word) :
    Except Fault Nat → Prop where
  | misaligned (bad : address.toNat % width ≠ 0) : CheckSpec memory domain access address
      (.error .misaligned)
  | denied (aligned : address.toNat % width = 0) (denied : ¬ Allowed memory domain access address) :
      CheckSpec memory domain access address (.error .accessDenied)
  | outside (aligned : address.toNat % width = 0) (allowed : Allowed memory domain access address)
      (outside : ¬ Backed memory address) :
      CheckSpec memory domain access address (.error .outOfBounds)
  | ready (aligned : address.toNat % width = 0) (allowed : Allowed memory domain access address)
      (backed : Backed memory address) : CheckSpec memory domain access address
        (.ok (address.toNat - memory.base))
-- ANCHOR_END: checkSemantics

-- ANCHOR: byteSpecification
def SameLayout (before after : Memory) : Prop :=
  after.base = before.base ∧ after.regions = before.regions ∧ after.bytes.size = before.bytes.size

def Loaded (memory : Memory) (offset : Nat) (value : Word) : Prop :=
  ∀ index : Nat, index < width → memory.bytes[offset + index]? = some (byteOf value index)

def Stored (before after : Memory) (offset : Nat) (value : Word) : Prop :=
  SameLayout before after ∧
  ∀ index : Nat, index < before.bytes.size →
    after.bytes[index]? =
      if offset ≤ index ∧ index < offset + width then some (byteOf value (index - offset))
      else before.bytes[index]?
-- ANCHOR_END: byteSpecification

-- ANCHOR: operationSemantics
inductive Step (domain : Domain) : Memory → Command → Reply → Memory → Prop where
  | failure (failed : CheckSpec memory domain command.access command.address (.error reason)) :
      Step domain memory command (.fault reason) memory
  | load (checked : CheckSpec memory domain .read address (.ok offset))
      (decoded : Loaded memory offset value) :
      Step domain memory (.load address) (.loaded value) memory
  | store (checked : CheckSpec before domain .write address (.ok offset))
      (updated : Stored before after offset value) :
      Step domain before (.store address value) .stored after

inductive Trace (domain : Domain) : Memory → List Command → List Reply → Memory → Prop where
  | nil : Trace domain memory [] [] memory
  | cons (first : Step domain before command reply middle)
      (rest : Trace domain middle commands replies after) :
      Trace domain before (command :: commands) (reply :: replies) after
-- ANCHOR_END: operationSemantics

end Course.ProtectedMemory
