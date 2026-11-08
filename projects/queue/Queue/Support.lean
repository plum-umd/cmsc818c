import Std

namespace Course.Queue.Support

-- ANCHOR: slotInjectivity
/-- Within one turn of a nonempty ring, different logical positions use different slots. -/
theorem slot_injective {head capacity i j : Nat}
    (headBound : head < capacity) (iBound : i < capacity)
    (jBound : j < capacity)
    (same : (head + i) % capacity = (head + j) % capacity) : i = j := by
  rw [Nat.add_mod_eq_ite, Nat.add_mod_eq_ite] at same
  simp only [Nat.mod_eq_of_lt headBound, Nat.mod_eq_of_lt iBound,
    Nat.mod_eq_of_lt jBound] at same
  split at same <;> split at same <;> omega
-- ANCHOR_END: slotInjectivity

end Course.Queue.Support
