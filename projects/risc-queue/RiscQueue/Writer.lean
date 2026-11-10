import RiscQueue.Native

namespace Course.RiscQueue.Ring

open Plos.RiscV

theorem writeSetup (ring : Ring) (index : Nat) (value : Word) :
    (writeCall ring index value).prepare { memory := ring.memory } =
      .ok (writePrepared ring index value) := by
  simp [writePrepared, writeCall, Append.invocation, Call.prepare]; rfl

theorem write_correct (ring : Ring) (valid : ring.Valid) (index : Nat) (value : Word)
    (inside : index < ring.capacity) :
    Append.Correct (ring.cells.take index) ring.capacity 256 value 192
      (writePrepared ring index value) (ring.writeResult index value) := by
  have length : (ring.cells.take index).length = index := by
    simp only [List.length_take, cells_length, Nat.min_eq_left (Nat.le_of_lt inside)]
  have buffer : Append.Buffer ring.memory .user 256 (ring.cells.take index) ring.capacity := by
    refine ⟨(ring.table valid).prefix index, by rw [length]; omega, valid.fits, ?_, ?_⟩
    · intro _
      simpa only [length] using ring.memory.load_mapped .user .read
        (256 + BitVec.ofNat 64 (8*index)) .double
          (ring.slot_mapped valid index inside .read (by decide))
    · intro _
      simpa only [length] using ring.memory.store64_mapped .user
        (256 + BitVec.ofNat 64 (8*index)) 0
          (ring.slot_mapped valid index inside .write (by decide))
  exact (Append.call_correct { memory := ring.memory } (writePrepared ring index value)
    128 192 256 0 value (ring.cells.take index) ring.capacity Append.allowance
    (by simpa only [length] using writeSetup ring index value)
    valid.appendCode ⟨by decide, by decide⟩ buffer (Or.inl (by decide)) (Nat.le_refl _)).2

theorem write_returns (ring : Ring) (valid : ring.Valid) (index : Nat) (value : Word)
    (inside : index < ring.capacity) : (ring.writeResult index value).stop = .returned :=
  (write_correct ring valid index value inside).1

theorem write_effect (ring : Ring) (valid : ring.Valid) (index : Nat) (value : Word)
    (inside : index < ring.capacity) :
    Store64Effect ring.memory (ring.writeResult index value).state.memory
      (256 + BitVec.ofNat 64 (8*index)) value := by
  have length : (ring.cells.take index).length = index := by
    simp only [List.length_take, cells_length, Nat.min_eq_left (Nat.le_of_lt inside)]
  have effect := (write_correct ring valid index value inside).2.2.2.2.2
  simp only [length, if_pos inside] at effect
  have memory := (Call.prepare_spec _ _ _ (writeSetup ring index value)).2.2.2.1
  simpa only [memory, length] using effect.2.2.2

end Course.RiscQueue.Ring
