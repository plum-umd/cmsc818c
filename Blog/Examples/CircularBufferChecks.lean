import Blog.Examples.CircularBuffer

namespace Course.Queue.Buffer.Checks

/-- A wrapped buffer with one unused slot containing an arbitrary old value. -/
def wrapped : State := ⟨#[9, 99, 7, 8], 2, 3⟩

example : Rep 4 wrapped [7, 8, 9] := by
  unfold Rep Valid view contents wrapped
  decide

example : push wrapped 10 = (.ok, ⟨#[9, 10, 7, 8], 2, 4⟩) := by decide

example : pop (push wrapped 10).2 = (.value 7, ⟨#[9, 10, 7, 8], 3, 3⟩) := by decide

/-- Capacity one exercises full and empty cases without reserving a spare array slot. -/
example :
    let result := runTrace (empty 1) [.push 0, .push 99, .pop, .pop]
    (result.1, view result.2) = ([.ok, .full, .value 0, .empty], []) := by decide

/-- Repeated values, rejected push, wraparound, stored zero, and repeated empty pop. -/
example :
    let result := runTrace (empty 2)
      [.push 7, .push 7, .push 9, .pop, .push 0, .pop, .pop, .pop, .pop]
    (result.1, view result.2) =
      ([.ok, .ok, .full, .value 7, .ok, .value 7, .value 0, .empty, .empty], []) := by decide

/-- The original six-command specification trace. -/
example :
    let result := runTrace (empty 2) [.push 7, .push 9, .push 11, .pop, .pop, .pop]
    (result.1, view result.2) =
      ([.ok, .ok, .full, .value 7, .value 9, .empty], []) := by decide

end Course.Queue.Buffer.Checks
