namespace Course.Queue

abbrev Word := UInt64

inductive Command where
  | push (value : Word)
  | pop
  deriving Repr, DecidableEq

inductive Reply where
  | ok
  | full
  | empty
  | value (word : Word)
  deriving Repr, DecidableEq

def Valid (capacity : Nat) (queue : List Word) : Prop := queue.length ≤ capacity

inductive Step (capacity : Nat) : List Word → Command → Reply → List Word → Prop where
  | push (room : queue.length < capacity) :
      Step capacity queue (.push value) .ok (queue ++ [value])
  | full (full : queue.length = capacity) :
      Step capacity queue (.push value) .full queue
  | pop : Step capacity (value :: rest) .pop (.value value) rest
  | empty : Step capacity [] .pop .empty []

theorem step_preserves (valid : Valid capacity queue)
    (step : Step capacity queue command reply next) : Valid capacity next := by
  cases step <;> simp_all [Valid, List.length_append] <;> omega

inductive Reachable (capacity : Nat) : List Word → Prop where
  | initial : Reachable capacity []
  | next : Reachable capacity queue → Step capacity queue command reply next →
      Reachable capacity next

theorem reachable_valid (reach : Reachable capacity queue) : Valid capacity queue := by
  induction reach with
  | initial => simp [Valid]
  | next _ step ih => exact step_preserves ih step

def run (capacity : Nat) (queue : List Word) : Command → Reply × List Word
  | .push value =>
      if queue.length < capacity then (.ok, queue ++ [value]) else (.full, queue)
  | .pop =>
      match queue with
      | [] => (.empty, [])
      | value :: rest => (.value value, rest)

theorem run_sound (valid : Valid capacity queue) (command : Command) :
    Step capacity queue command (run capacity queue command).1
      (run capacity queue command).2 := by
  cases command with
  | push value =>
    by_cases room : queue.length < capacity
    · simpa [run, room] using (Step.push (value := value) room)
    · have full : queue.length = capacity := by unfold Valid at valid; omega
      simpa [run, room] using (Step.full (value := value) full)
  | pop =>
    cases queue with
    | nil => exact Step.empty
    | cons value rest => exact Step.pop

theorem step_run (step : Step capacity queue command reply next) :
    run capacity queue command = (reply, next) := by
  cases step <;> simp_all [run]

theorem step_iff_run (valid : Valid capacity queue) :
    Step capacity queue command reply next ↔ run capacity queue command = (reply, next) := by
  constructor
  · exact step_run
  · intro result
    have step := run_sound valid command
    rw [result] at step
    exact step

theorem step_deterministic (first : Step capacity queue command reply₁ next₁)
    (second : Step capacity queue command reply₂ next₂) :
    reply₁ = reply₂ ∧ next₁ = next₂ := by
  have same := (step_run first).symm.trans (step_run second)
  exact Prod.mk.inj same

end Course.Queue
