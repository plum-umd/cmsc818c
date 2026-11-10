import RiscQueue.API
import Plos.Kernel.Components

namespace Course.RiscQueue.Policy

open Plos.RiscV

-- ANCHOR: queue
/-- Native states carry validity evidence; fallback preserves arbitrary natural-number PIDs. -/
inductive Queue where
  | native (ring : Ring) (valid : ring.Valid)
  | fallback (pids : List Nat)

def view : Queue → List Nat
  | .native ring _ => ring.view
  | .fallback pids => pids

/-- Admission and growth occur on the host; no unrepresentable PID is silently truncated. -/
def fromList (pids : List Nat) : Queue :=
  let capacity := max 4 (2*pids.length)
  if fits : 256 + 8*capacity ≤ 2^64 ∧ pids.all (fun pid => decide (pid < 2^64)) = true then
    .native (Ring.init (pids.map (BitVec.ofNat 64)) capacity)
      (Ring.init_valid _ _ (by omega) (by simp only [List.length_map]; omega) fits.1)
  else .fallback pids
-- ANCHOR_END: queue

def reserve : Queue → Queue
  | .native ring valid =>
    if ring.count < ring.capacity then .native ring valid else fromList ring.view
  | .fallback pids => .fallback pids

-- ANCHOR: enqueue
def pushFresh (correct : CorrectRing) : Queue → Nat → Queue
  | .native ring valid, pid =>
    if room : ring.count < ring.capacity ∧ pid < 2^64 then
      .native (ring.push (BitVec.ofNat 64 pid)) (correct.push ring _ valid room.1).valid
    else .fallback (ring.view ++ [pid])
  | .fallback pids, pid => .fallback (pids ++ [pid])

def enqueue (correct : CorrectRing) (queue : Queue) (pid : Nat) : Queue :=
  if (Plos.Kernel.RunQueue.contains ⟨view queue⟩ pid) then queue
  else pushFresh correct (reserve queue) pid
-- ANCHOR_END: enqueue

-- ANCHOR: dequeue
def dequeue (correct : CorrectRing) : Queue → Option (Nat × Queue)
  | .fallback [] => none
  | .fallback (pid :: rest) => some (pid, .fallback rest)
  | .native ring valid =>
    if empty : ring.count = 0 then none
    else some (ring.pop.1.toNat, .native ring.pop.2 (correct.pop ring valid (by omega)).valid)

def remove (queue : Queue) (pid : Nat) : Queue :=
  fromList ((view queue).filter (fun p => decide (p ≠ pid)))

def isEmpty : Queue → Bool
  | .native ring _ => ring.count == 0
  | .fallback pids => pids.isEmpty
-- ANCHOR_END: dequeue

-- ANCHOR: ops
def ops (correct : CorrectRing) : Plos.Kernel.Components.QueueOps where
  State := Queue
  empty := fromList []
  enqueue := enqueue correct
  dequeue := dequeue correct
  remove := remove
  isEmpty := isEmpty
-- ANCHOR_END: ops

end Course.RiscQueue.Policy
