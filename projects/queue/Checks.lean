import Queue

open Course.Queue

private def wrapped : Buffer.State := ⟨#[9, 99, 7, 8], 2, 3⟩

#guard Buffer.view wrapped = [7, 8, 9]
#guard Buffer.push wrapped 10 = (.ok, ⟨#[9, 10, 7, 8], 2, 4⟩)
#guard Buffer.pop (Buffer.push wrapped 10).2 = (.value 7, ⟨#[9, 10, 7, 8], 3, 3⟩)
#guard Buffer.push (Buffer.push wrapped 10).2 11 = (.full, (Buffer.push wrapped 10).2)
#guard Buffer.pop (Buffer.empty 2) = (.empty, Buffer.empty 2)

-- Stored zero is a value; every slot is usable, even at capacity one.
#guard
  let result := Buffer.runTrace (Buffer.empty 1) [.push 0, .push 99, .pop, .pop]
  (result.1, Buffer.view result.2) = ([.ok, .full, .value 0, .empty], [])

-- Duplicate values are legitimate; a rejected push must not discard an old value.
#guard
  let result := Buffer.runTrace (Buffer.empty 2)
    [.push 7, .push 7, .push 9, .pop, .push 0, .pop, .pop, .pop]
  (result.1, Buffer.view result.2) =
    ([.ok, .ok, .full, .value 7, .ok, .value 7, .value 0, .empty], [])

-- Differential examples include the full concrete representation, not just reply counts.
#guard
  let commands := [.push 7, .push 9, .push 11, .pop, .push 12, .pop, .pop, .pop]
  let actual := Buffer.runTrace (Buffer.empty 2) commands
  (actual.1, Buffer.view actual.2) = Buffer.referenceTrace 2 [] commands

-- Zero capacity has defined executable behavior but is outside the representation invariant.
#guard Buffer.runTrace (Buffer.empty 0) [.push 7, .pop] =
  ([.full, .empty], Buffer.empty 0)
