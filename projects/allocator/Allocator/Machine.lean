import Std

namespace Course.Allocator

-- ANCHOR: machineWords
abbrev Word := BitVec 64

def addressLimit : Nat := 2 ^ 64

def wordBytes : Nat := 8
-- ANCHOR_END: machineWords

/-- A half-open interval of byte addresses, described without wrapping arithmetic. -/
-- ANCHOR: blocks
structure Block where
  start : Word
  size : Nat
  deriving DecidableEq, Repr

def Block.finish (block : Block) : Nat := block.start.toNat + block.size

def Block.Contains (block : Block) (address : Nat) : Prop :=
  block.start.toNat ≤ address ∧ address < block.finish

def Block.Disjoint (left right : Block) : Prop :=
  left.finish ≤ right.start.toNat ∨ right.finish ≤ left.start.toNat
-- ANCHOR_END: blocks

/-- Finite byte backing at an absolute base address, as in the PL/OS RISC model. -/
-- ANCHOR: memory
structure Memory where
  base : Nat
  bytes : Array UInt8
  deriving DecidableEq, Repr

def Memory.finish (memory : Memory) : Nat := memory.base + memory.bytes.size
-- ANCHOR_END: memory

end Course.Allocator
