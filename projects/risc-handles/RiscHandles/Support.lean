import RiscHandles.Spec

namespace Course.RiscHandles.Support

open Plos.RiscV

/-- Ordinary addresses for cells strictly inside a nonwrapping buffer. -/
theorem slot_address (address : Word) (capacity index : Nat)
    (fits : address.toNat + 8 * capacity ≤ 2^64) (inside : index < capacity) :
    (address + BitVec.ofNat 64 (8 * index)).toNat = address.toNat + 8 * index := by
  have small : 8 * index < 2^64 := by omega
  have total : address.toNat + 8 * index < 2^64 := by omega
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt total]

/-- Instruction addresses within the installed image are not completed calls. -/
theorem not_return {memory : Memory} {mode : Mode} {base ret : Word}
    {code : Array InstructionWord} (image : CodeAt memory mode base code)
    (location : ReturnAt base ret code) (offset : Nat) (inside : offset < 4 * code.size) :
    base + BitVec.ofNat 64 offset ≠ ret := by
  have address := image.address offset inside
  intro same
  rw [same] at address
  have := location.outside
  omega

end Course.RiscHandles.Support
