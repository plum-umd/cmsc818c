import RiscQueue.Spec

namespace Course.RiscQueue.View

open Plos.RiscV

-- ANCHOR: view
/-- One wrap suffices for an active offset below capacity and a valid head. -/
def slot (head capacity offset : Nat) : Nat :=
  if head + offset < capacity then head + offset else head + offset - capacity

def words (cells : List Word) (head count capacity : Nat) : List Word :=
  let snapshot := cells.toArray
  (List.range count).map fun i => snapshot[slot head capacity i]!
-- ANCHOR_END: view

@[simp] theorem length (cells : List Word) (head count capacity : Nat) :
    (words cells head count capacity).length = count := by simp [words]

theorem slot_bound (head capacity offset : Nat) (h : head < capacity) (i : offset < capacity) :
    slot head capacity offset < capacity := by unfold slot; split <;> omega

theorem slot_injective (head capacity i j : Nat) (hi : i < capacity) (hj : j < capacity)
    (same : slot head capacity i = slot head capacity j) : i = j := by
  unfold slot at same
  split at same <;> split at same <;> omega

@[simp] theorem slot_zero (head capacity : Nat) (h : head < capacity) :
    slot head capacity 0 = head := by simp [slot, h]

theorem slot_next (head capacity i : Nat) (h : head < capacity) (hi : i < capacity) :
    slot (nextHead head capacity) capacity i = slot head capacity (i+1) := by
  unfold slot nextHead
  split <;> split <;> split <;> omega

end Course.RiscQueue.View
