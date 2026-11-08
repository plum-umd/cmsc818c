import CooperativeKernel
import CooperativeKernel.Examples

open Course.CooperativeKernel Course.CooperativeKernel.Examples

example : initial.Valid := by
  unfold Kernel.Valid Spec.Valid ValidTable
  decide

-- The running process has advanced beyond its parked snapshot.
#guard (initial.entry 0).context ≠ initial.cpu
#guard ((view initial).entry 0).context = initial.cpu

private def first : Kernel := (handle initial .yield).2
#guard (handle initial .yield).1 = .running 1
#guard first.ready = [2, 0]
#guard first.cpu = (initial.entry 1).context
#guard first.activeDomain = some .right
#guard (first.entry 0).context = initial.cpu
#guard (first.entry 2).context = (initial.entry 2).context

-- Three yields return to the saved computation, including every register and the PC.
#guard
  let result := runEvents initial [.yield, .yield, .yield]
  result.1 = [.running 1, .running 2, .running 0] ∧ result.2.cpu = initial.cpu ∧
    result.2.activeDomain = some .left ∧ result.2.ready = [1, 2]

-- Exiting does not enqueue the departing process. Its final context is archived.
private def departed : Kernel := (handle initial .exit).2
#guard departed.ready = [2]
#guard (departed.entry 0).status = .exited
#guard (departed.entry 0).context = initial.cpu
#guard departed.current = some 1

private def lastProcess : Kernel := (runEvents initial [.exit, .exit]).2
#guard lastProcess.current = some 2
#guard lastProcess.ready = []
#guard (handle lastProcess .yield).1 = .running 2
#guard (handle lastProcess .yield).2.cpu = lastProcess.cpu

private def finished : Kernel := (runEvents initial [.exit, .exit, .exit]).2
#guard finished.current = none
#guard finished.activeDomain = none
#guard finished.ready = []
#guard finished.memory = initial.memory
#guard handle finished .yield = (.idle, finished)
#guard handle finished .exit = (.idle, finished)

#guard
  let result := runEvents initial [.exit, .yield, .yield, .yield]
  result.1 = [.running 1, .running 2, .running 1, .running 2] ∧
    (result.2.entry 0).status = .exited
