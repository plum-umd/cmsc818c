import Std

namespace Course.ProtectedMemory

abbrev Word := BitVec 64
def width : Nat := 8
def addressLimit : Nat := 2 ^ 64

-- ANCHOR: memoryPolicy
inductive Domain where
  | left | right
  deriving DecidableEq, Repr

inductive Access where
  | read | write
  deriving DecidableEq, Repr

structure Region where
  start : Nat
  size : Nat
  owner : Domain
  readable : Bool
  writable : Bool
  deriving DecidableEq, Repr

def Region.finish (region : Region) : Nat := region.start + region.size

structure Memory where
  base : Nat
  bytes : Array UInt8
  regions : List Region
  deriving DecidableEq, Repr

def Memory.finish (memory : Memory) : Nat := memory.base + memory.bytes.size
-- ANCHOR_END: memoryPolicy

-- ANCHOR: accessSpecification
def Region.Covers (region : Region) (domain : Domain) (access : Access) (address : Word) : Prop :=
  region.owner = domain ∧ region.start ≤ address.toNat ∧
    address.toNat + width ≤ region.finish ∧ address.toNat + width ≤ addressLimit ∧
    (match access with | .read => region.readable | .write => region.writable) = true

instance (region : Region) (domain : Domain) (access : Access) (address : Word) :
    Decidable (region.Covers domain access address) := by
  unfold Region.Covers
  infer_instance

def Allowed (memory : Memory) (domain : Domain) (access : Access) (address : Word) : Prop :=
  ∃ region ∈ memory.regions, region.Covers domain access address

def Backed (memory : Memory) (address : Word) : Prop :=
  memory.base ≤ address.toNat ∧ address.toNat + width ≤ memory.finish ∧
    address.toNat + width ≤ addressLimit

instance (memory : Memory) (address : Word) : Decidable (Backed memory address) := by
  unfold Backed
  infer_instance
-- ANCHOR_END: accessSpecification

-- ANCHOR: validPolicy
def Isolated (regions : List Region) : Prop :=
  ∀ left ∈ regions, ∀ right ∈ regions, left.owner ≠ right.owner →
    left.finish ≤ right.start ∨ right.finish ≤ left.start

def Memory.Valid (memory : Memory) : Prop :=
  memory.finish ≤ addressLimit ∧
  (∀ region ∈ memory.regions, memory.base ≤ region.start ∧ region.finish ≤ memory.finish) ∧
  Isolated memory.regions

def Owned (memory : Memory) (domain : Domain) (address : Nat) : Prop :=
  ∃ region ∈ memory.regions,
    region.owner = domain ∧ region.start ≤ address ∧ address < region.finish

def byteAt (memory : Memory) (address : Nat) : Option UInt8 :=
  if memory.base ≤ address then memory.bytes[address - memory.base]? else none
-- ANCHOR_END: validPolicy

inductive Fault where
  | misaligned | accessDenied | outOfBounds
  deriving DecidableEq, Repr

-- ANCHOR: checkAccess
def check (memory : Memory) (domain : Domain) (access : Access) (address : Word) :
    Except Fault Nat :=
  if address.toNat % width ≠ 0 then .error .misaligned
  else if memory.regions.any (fun region => decide (region.Covers domain access address)) then
    if Backed memory address then .ok (address.toNat - memory.base)
    else .error .outOfBounds
  else .error .accessDenied
-- ANCHOR_END: checkAccess

-- ANCHOR: byteEncoding
def byteOf (value : Word) (index : Nat) : UInt8 :=
  UInt8.ofNat (value.toNat / 2 ^ (8 * index))

def readWord (bytes : Array UInt8) (offset : Nat) : Word :=
  BitVec.ofNat 64 <| (List.range width).foldl
    (fun value index => value + (bytes[offset + index]?.getD 0).toNat * 2 ^ (8 * index)) 0

def writeWord (bytes : Array UInt8) (offset : Nat) (value : Word) : Array UInt8 :=
  (List.range width).foldl
    (fun bytes index => bytes.setIfInBounds (offset + index) (byteOf value index)) bytes
-- ANCHOR_END: byteEncoding

-- ANCHOR: operations
inductive Command where
  | load (address : Word)
  | store (address value : Word)
  deriving DecidableEq, Repr

def Command.access : Command → Access
  | .load _ => .read
  | .store .. => .write

def Command.address : Command → Word
  | .load address | .store address _ => address

inductive Reply where
  | loaded (value : Word)
  | stored
  | fault (reason : Fault)
  deriving DecidableEq, Repr

def operate (memory : Memory) (domain : Domain) (command : Command) : Reply × Memory :=
  match command with
  | .load address =>
      match check memory domain .read address with
      | .error reason => (.fault reason, memory)
      | .ok offset => (.loaded (readWord memory.bytes offset), memory)
  | .store address value =>
      match check memory domain .write address with
      | .error reason => (.fault reason, memory)
      | .ok offset => (.stored, { memory with bytes := writeWord memory.bytes offset value })

def runTrace (memory : Memory) (domain : Domain) : List Command → List Reply × Memory
  | [] => ([], memory)
  | command :: commands =>
      let (reply, next) := operate memory domain command
      let (replies, final) := runTrace next domain commands
      (reply :: replies, final)
-- ANCHOR_END: operations

end Course.ProtectedMemory
