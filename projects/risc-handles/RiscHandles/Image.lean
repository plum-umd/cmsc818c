import RiscHandles.Spec

-- Adapted from the pinned PL/OS HandleImage loader to admit arbitrary student append code.

namespace Course.RiscHandles.Image

open Plos.RiscV

/-- Fixed disjoint code mappings and a writable dense buffer. -/
def regions (image : Array InstructionWord) (capacity : Nat) : List Region := [
  ⟨0, 44, true, false, true, true⟩, ⟨64, 4*image.size, true, false, true, true⟩,
  ⟨256, 8*capacity, true, true, false, true⟩]

private def contents (image : Array InstructionWord) (channels : Array Word) (j : Nat) : UInt8 :=
  if j < 44 then UInt8.ofNat (Lookup.code[j / 4]!.toNat / 2^(8*(j % 4)))
  else if 64 ≤ j ∧ j < (64 + 4*image.size) then
    UInt8.ofNat (image[(j-64) / 4]!.toNat / 2^(8*((j-64) % 4)))
  else if j < 256 then 0
  else UInt8.ofNat ((channels[(j-256) / 8]?.getD 0).toNat / 2^(8*((j-256) % 8)))

/-- Lookup at zero, append at 64, and a zero-padded buffer at 256. -/
@[irreducible] def memory (image : Array InstructionWord) (channels : List Word)
    (capacity : Nat) : Memory :=
  let cells := channels.toArray
  { bytes := Array.ofFn (n := 256 + 8*capacity) fun j => contents image cells j.val
    regions := regions image capacity }

@[simp] theorem memory_base (image : Array InstructionWord) (channels : List Word)
    (capacity : Nat) :
    (memory image channels capacity).base = 0 := by
  unfold memory
  rfl

@[simp] theorem memory_size (image : Array InstructionWord) (channels : List Word)
    (capacity : Nat) :
    (memory image channels capacity).bytes.size = 256 + 8*capacity := by
  simp [memory, regions]

private theorem byte (image : Array InstructionWord) (channels : List Word)
    (capacity index : Nat)
    (inside : index < 256 + 8*capacity) :
    (memory image channels capacity).bytes[index]! = contents image channels.toArray index := by
  rw [getElem!_pos (memory image channels capacity).bytes index
    (by rw [memory_size]; exact inside)]
  simp only [memory, Array.getElem_ofFn]

private theorem code_byte (image : Array InstructionWord) (channels : List Word)
    (capacity i j : Nat)
    (hi : i < 11) (hj : j < 4) :
    (memory image channels capacity).bytes[4*i+j]! =
      UInt8.ofNat (Lookup.code[i]!.toNat / 2^(8*j)) := by
  rw [byte image channels capacity _ (by omega)]
  simp only [contents, show 4*i+j < 44 by omega, if_true]
  rw [show (4*i+j)/4 = i by omega, show (4*i+j)%4 = j by omega]

private theorem table_byte (image : Array InstructionWord) (codeBound : image.size ≤ 16)
    (channels : List Word) (capacity i j : Nat) (channel : Word)
    (length : channels.length ≤ capacity) (found : channels[i]? = some channel) (hj : j < 8) :
    (memory image channels capacity).bytes[256+8*i+j]! = UInt8.ofNat (channel.toNat / 2^(8*j)) := by
  have hi := (List.getElem?_eq_some_iff.mp found).1
  rw [byte image channels capacity _ (by omega)]
  simp only [contents, show ¬ 256+8*i+j < 44 by omega,
    show ¬ (64 ≤ 256+8*i+j ∧ 256+8*i+j < (64 + 4*image.size)) by omega,
    show ¬ 256+8*i+j < 256 by omega, if_false]
  rw [show (256+8*i+j-256)/8 = i by omega, show (256+8*i+j-256)%8 = j by omega]
  simp only [List.getElem?_toArray, found, Option.getD_some]

/-- The serialized code is installed under actual executable-memory checks. -/
theorem lookup_code (image : Array InstructionWord) (channels : List Word) (capacity : Nat) :
    Lookup.Code (memory image channels capacity) .user 0 := by
  refine ⟨by decide, by decide +kernel, ?_⟩
  intro i
  have codeSize : Lookup.code.size = 11 := by decide +kernel
  have hi : i.val < 11 := by simpa only [codeSize] using i.isLt
  have address : (0 + BitVec.ofNat 64 (4*i.val)).toNat = 4*i.val := by
    simp [Nat.mod_eq_of_lt (show 4*i.val < 2^64 by omega)]
  have value : (BitVec.ofNat 64 Lookup.code[i.val].toNat).toNat = Lookup.code[i.val].toNat := by
    have := Lookup.code[i.val].isLt
    simp [Nat.mod_eq_of_lt (show Lookup.code[i.val].toNat < 2^64 by omega)]
  rw [← value]
  apply (memory image channels capacity).load_encoded .user .execute _ .word _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change _ % 4 = 0
      rw [address]
      omega
    · simp
    · change _ + 4 ≤ _
      simp only [address, memory_base, memory_size]
      omega
    · refine ⟨⟨0, 44, true, false, true, true⟩, ?_, ?_⟩
      · simp [memory, regions]
      · simp only [address, Width.byteCount]
        exact ⟨by omega, by omega, by omega, by simp, by simp⟩
  · change _ < 2^32
    rw [value]
    exact Lookup.code[i.val].isLt
  · intro j hj
    change j < 4 at hj
    simp only [address, memory_base, Nat.sub_zero]
    rw [value]
    simpa only [getElem!_pos Lookup.code i.val i.isLt] using
      code_byte image channels capacity i.val j hi hj

private theorem append_byte (image : Array InstructionWord) (codeBound : image.size ≤ 16)
    (channels : List Word) (capacity i j : Nat)
    (hi : i < image.size) (hj : j < 4) :
    (memory image channels capacity).bytes[64+4*i+j]! =
      UInt8.ofNat (image[i]!.toNat / 2^(8*j)) := by
  rw [byte image channels capacity _ (by omega)]
  simp only [contents, show ¬ 64+4*i+j < 44 by omega, if_false,
    show 64 ≤ 64+4*i+j ∧ 64+4*i+j < (64 + 4*image.size) by omega, and_self, if_true]
  rw [show (64+4*i+j-64)/4 = i by omega, show (64+4*i+j-64)%4 = j by omega]

/-- The serialized code is installed under actual executable-memory checks. -/
theorem append_code (image : Array InstructionWord) (codeBound : image.size ≤ 16)
    (channels : List Word) (capacity : Nat) :
    CodeAt (memory image channels capacity) .user 64 image := by
  refine ⟨by decide, by change 64 + 4*image.size ≤ 2^64; omega, ?_⟩
  intro i
  have hi : i.val < image.size := i.isLt
  have address : (64 + BitVec.ofNat 64 (4*i.val)).toNat = 64+4*i.val := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt (show 4*i.val < 2^64 by omega),
      Nat.mod_eq_of_lt (show 64+4*i.val < 2^64 by omega)]
  have value : (BitVec.ofNat 64 image[i.val].toNat).toNat = image[i.val].toNat := by
    have := image[i.val].isLt
    simp [Nat.mod_eq_of_lt (show image[i.val].toNat < 2^64 by omega)]
  rw [← value]
  apply (memory image channels capacity).load_encoded .user .execute _ .word _
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change _ % 4 = 0
      rw [address]
      omega
    · simp
    · change _ + 4 ≤ _
      simp only [address, memory_base, memory_size]
      omega
    · refine ⟨⟨64, 4*image.size, true, false, true, true⟩, ?_, ?_⟩
      · simp [memory, regions]
      · simp only [address, Width.byteCount]
        exact ⟨by omega, by omega, by omega, by simp, by simp⟩
  · change _ < 2^32
    rw [value]
    exact image[i.val].isLt
  · intro j hj
    change j < 4 at hj
    simp only [address, memory_base, Nat.sub_zero]
    rw [value]
    simpa only [getElem!_pos image i.val i.isLt] using
      append_byte image codeBound channels capacity i.val j hi hj

/-- Every serialized table cell is readable with its original word value. -/
theorem table (image : Array InstructionWord) (codeBound : image.size ≤ 16)
    (channels : List Word) (capacity : Nat) (length : channels.length ≤ capacity)
    (fits : 256 + 8*capacity ≤ 2^64) :
    Lookup.Table (memory image channels capacity) .user 256 channels := by
  refine ⟨by change 256 + 8*channels.length ≤ 2^64; omega, ?_⟩
  intro index channel found
  have hi := (List.getElem?_eq_some_iff.mp found).1
  have small : 256 + 8*index < 2^64 := by omega
  have address : (256 + BitVec.ofNat 64 (8*index)).toNat = 256 + 8*index := by
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt small,
      Nat.mod_eq_of_lt (show 8*index < 2^64 by omega)]
  apply (memory image channels capacity).load_encoded .user .read _ .double channel
  · refine ⟨?_, ?_, ?_, ?_⟩
    · change _ % 8 = 0
      rw [address]
      omega
    · simp
    · change _ + 8 ≤ _
      simp only [address, memory_base, memory_size]
      omega
    · refine ⟨⟨256, 8*capacity, true, true, false, true⟩, ?_, ?_⟩
      · simp [memory, regions]
      · simp only [address, Width.byteCount]
        exact ⟨by omega, by omega, by omega, by simp, by simp⟩
  · exact channel.isLt
  · intro j hj
    change j < 8 at hj
    simp only [address, memory_base, Nat.sub_zero]
    exact table_byte image codeBound channels capacity index j channel length found hj

end Course.RiscHandles.Image
