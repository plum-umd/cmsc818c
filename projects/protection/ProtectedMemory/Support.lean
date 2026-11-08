import ProtectedMemory.Model

namespace Course.ProtectedMemory.Support

theorem writeWord_size (bytes : Array UInt8) (offset : Nat) (value : Word) :
    (writeWord bytes offset value).size = bytes.size := by
  unfold writeWord
  generalize List.range width = indices
  induction indices generalizing bytes with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.foldl_cons]
      rw [ih, Array.size_setIfInBounds]

theorem byte_prefix (value : Word) (count : Nat) :
    (List.range count).foldl (fun n i => n + (byteOf value i).toNat * 2^(8*i)) 0 =
      value.toNat % 2^(8*count) := by
  induction count with
  | zero => exact (Nat.mod_one _).symm
  | succ count ih =>
      rw [List.range_succ, List.foldl_append]
      change ((List.range count).foldl _ 0) + (byteOf value count).toNat * 2^(8*count) = _
      rw [ih]
      simp only [byteOf, UInt8.toNat_ofNat']
      rw [show 2^(8*(count+1)) = 2^(8*count) * 256 by
        simp [Nat.mul_add, Nat.pow_add], Nat.mod_mul]
      rw [Nat.mul_comm (value.toNat / 2^(8*count) % 2^8)]

-- ANCHOR: byteRoundtrip
theorem byte_roundtrip (value : Word) :
    (List.range 8).foldl (fun n i => n + (byteOf value i).toNat * 2^(8*i)) 0 = value.toNat := by
  rw [byte_prefix]
  exact Nat.mod_eq_of_lt value.isLt
-- ANCHOR_END: byteRoundtrip

end Course.ProtectedMemory.Support
