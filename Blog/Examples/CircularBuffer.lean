import Queue.Buffer

namespace Course.Queue.Buffer

@[simp] theorem length_contents : (contents slots head count).length = count := by
  simp [contents]

@[simp] theorem length_view : (view buffer).length = buffer.count := by
  simp [view]

theorem rep_valid (rep : Rep capacity buffer queue) : Course.Queue.Valid capacity queue := by
  rcases rep with ⟨valid, rfl⟩
  simpa [Course.Queue.Valid] using valid.2.2.2

theorem empty_rep (positive : 0 < capacity) : Rep capacity (empty capacity) [] := by
  simp [Rep, Valid, empty, view, contents, positive]

theorem occupied_in_bounds (valid : Valid capacity buffer) :
    (buffer.head + i) % buffer.slots.size < buffer.slots.size := by
  rcases valid with ⟨positive, size, _, _⟩
  exact Nat.mod_lt _ (by omega)

/-- Logical positions within one turn of the ring denote different slots. -/
theorem slot_injective {head capacity i j : Nat}
    (headBound : head < capacity) (iBound : i < capacity)
    (jBound : j < capacity)
    (same : (head + i) % capacity = (head + j) % capacity) : i = j := by
  rw [Nat.add_mod_eq_ite, Nat.add_mod_eq_ite] at same
  simp only [Nat.mod_eq_of_lt headBound, Nat.mod_eq_of_lt iBound,
    Nat.mod_eq_of_lt jBound] at same
  split at same <;> split at same <;> omega

theorem contents_push (headBound : head < slots.size) (room : count < slots.size) :
    contents (slots.setIfInBounds ((head + count) % slots.size) value) head (count + 1) =
      contents slots head count ++ [value] := by
  unfold contents
  rw [List.range_succ, List.map_append]
  simp only [List.map_cons, List.map_nil, Array.size_setIfInBounds]
  have preserved :
      (List.range count).map (fun i =>
        (slots.setIfInBounds ((head + count) % slots.size)
          value)[(head + i) % slots.size]?.getD 0) =
      (List.range count).map (fun i => slots[(head + i) % slots.size]?.getD 0) := by
    apply List.map_congr_left
    intro i member
    have iBound : i < count := List.mem_range.mp member
    have distinct : (head + count) % slots.size ≠ (head + i) % slots.size := by
      intro same
      have := slot_injective headBound room (by omega) same
      omega
    simp [Array.getElem?_setIfInBounds_ne distinct]
  rw [preserved]
  simp [Nat.mod_lt _ (by omega : 0 < slots.size)]

theorem contents_pop (headBound : head < slots.size) :
    contents slots head (count + 1) =
      slots[head]?.getD 0 :: contents slots ((head + 1) % slots.size) count := by
  unfold contents
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, Nat.mod_eq_of_lt headBound]
  congr 1
  apply List.map_congr_left
  intro i _
  have index : (head + (i + 1)) % slots.size =
      ((head + 1) % slots.size + i) % slots.size := by
    rw [Nat.mod_add_mod]
    congr 1
    omega
  change slots[(head + (i + 1)) % slots.size]?.getD 0 = _
  rw [index]

theorem push_valid (valid : Valid capacity buffer) :
    Valid capacity (push buffer value).2 := by
  rcases valid with ⟨positive, size, headBound, countBound⟩
  unfold push
  split <;> simp_all [Valid] <;> omega

theorem pop_valid (valid : Valid capacity buffer) : Valid capacity (pop buffer).2 := by
  rcases valid with ⟨positive, size, headBound, countBound⟩
  unfold pop
  split
  · simpa [Valid] using And.intro positive ⟨size, headBound, countBound⟩
  · simp only [Valid]
    exact ⟨positive, size, by simpa [size] using Nat.mod_lt (buffer.head + 1) positive,
      by omega⟩

theorem run_valid (valid : Valid capacity buffer) (command : Command) :
    Valid capacity (run buffer command).2 := by
  cases command with
  | push value => exact push_valid valid
  | pop => exact pop_valid valid

theorem push_refines (valid : Valid capacity buffer) :
    ((push buffer value).1, view (push buffer value).2) =
      Course.Queue.run capacity (view buffer) (.push value) := by
  rcases valid with ⟨positive, size, headBound, countBound⟩
  have headInBounds : buffer.head < buffer.slots.size := by omega
  unfold push
  split
  · rename_i room
    have abstractRoom : buffer.count < capacity := by omega
    simp only [view, Course.Queue.run, length_contents, ite_eq_left abstractRoom]
    congr 1
    exact contents_push headInBounds room
  · rename_i full
    have abstractFull : ¬buffer.count < capacity := by omega
    simp [Course.Queue.run, length_view, abstractFull]

theorem pop_refines (valid : Valid capacity buffer) :
    ((pop buffer).1, view (pop buffer).2) =
      Course.Queue.run capacity (view buffer) .pop := by
  rcases valid with ⟨positive, size, headBound, countBound⟩
  have headInBounds : buffer.head < buffer.slots.size := by omega
  cases countEq : buffer.count with
  | zero => simp [pop, countEq, view, contents, Course.Queue.run]
  | succ count =>
    have shape : view buffer = buffer.slots[buffer.head]?.getD 0 ::
        contents buffer.slots ((buffer.head + 1) % buffer.slots.size) count := by
      simpa [view, countEq] using (contents_pop (count := count) headInBounds)
    rw [shape]
    simp [pop, countEq, Course.Queue.run, view]

theorem run_refines (valid : Valid capacity buffer) (command : Command) :
    ((run buffer command).1, view (run buffer command).2) =
      Course.Queue.run capacity (view buffer) command := by
  cases command with
  | push value => exact push_refines valid
  | pop => exact pop_refines valid

theorem push_full (valid : Valid capacity buffer) (full : buffer.count = capacity) :
    push buffer value = (.full, buffer) := by
  simp [push, valid.2.1, full]

theorem pop_empty (empty : buffer.count = 0) : pop buffer = (.empty, buffer) := by
  simp [pop, empty]

/-- Refinement to the independently defined transition relation, with a reusable next state. -/
theorem run_simulates (rep : Rep capacity buffer queue) (command : Command) :
    Step capacity queue command (run buffer command).1 (view (run buffer command).2) ∧
      Rep capacity (run buffer command).2 (view (run buffer command).2) := by
  constructor
  · apply (Course.Queue.step_iff_run (rep_valid rep)).2
    rw [← rep.2]
    exact (run_refines rep.1 command).symm
  · exact ⟨run_valid rep.1 command, rfl⟩

theorem trace_valid (valid : Valid capacity buffer) (commands : List Command) :
    Valid capacity (runTrace buffer commands).2 := by
  induction commands generalizing buffer with
  | nil => exact valid
  | cons command commands ih => exact ih (run_valid valid command)

theorem trace_refines (valid : Valid capacity buffer) (commands : List Command) :
    ((runTrace buffer commands).1, view (runTrace buffer commands).2) =
      referenceTrace capacity (view buffer) commands := by
  induction commands generalizing buffer with
  | nil => rfl
  | cons command commands ih =>
    have one := run_refines valid command
    have rest := ih (run_valid valid command)
    simp only [referenceTrace, runTrace]
    rw [← one]
    simp only
    rw [← rest]

theorem initialized_trace (positive : 0 < capacity) (commands : List Command) :
    Valid capacity (runTrace (empty capacity) commands).2 ∧
      ((runTrace (empty capacity) commands).1, view (runTrace (empty capacity) commands).2) =
        referenceTrace capacity [] commands := by
  have rep := empty_rep positive
  constructor
  · exact trace_valid rep.1 commands
  · simpa only [rep.2] using trace_refines rep.1 commands

end Course.Queue.Buffer
