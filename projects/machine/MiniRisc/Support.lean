import MiniRisc.Model

namespace Course.MiniRisc.Support

-- ANCHOR: decrement
theorem decrement_toNat (value : Word) (positive : 0 < value.toNat) :
    (value - 1).toNat = value.toNat - 1 := by
  have enough : (1 : Word) ≤ value := by
    change 1 ≤ value.toNat
    omega
  simpa using BitVec.toNat_sub_of_le enough
-- ANCHOR_END: decrement

end Course.MiniRisc.Support
