import MiniRisc.Model
import ProtectedMemory.Model

namespace Course.CooperativeKernel

-- ANCHOR: processModel
abbrev Pid := Fin 3
abbrev Context := Course.MiniRisc.State
abbrev Domain := Course.ProtectedMemory.Domain
abbrev Memory := Course.ProtectedMemory.Memory

inductive Status where
  | ready | running | exited
  deriving DecidableEq, Repr

structure Process where
  context : Context
  domain : Domain
  status : Status
  deriving DecidableEq, Repr

inductive Event where
  | yield | exit
  deriving DecidableEq, Repr

inductive Reply where
  | running (pid : Pid)
  | idle
  deriving DecidableEq, Repr

structure Spec where
  table : Vector Process 3
  current : Option Pid
  ready : List Pid
  memory : Memory
  deriving DecidableEq, Repr

def Spec.entry (spec : Spec) (pid : Pid) : Process := spec.table[pid.val]
-- ANCHOR_END: processModel

-- ANCHOR: schedulingInvariant
def ValidTable (table : Vector Process 3) (current : Option Pid) (ready : List Pid) : Prop :=
  ready.Nodup ∧
  (∀ pid : Pid, (table[pid.val]).status = .running ↔ current = some pid) ∧
  (∀ pid : Pid, pid ∈ ready ↔ (table[pid.val]).status = .ready) ∧
  (current = none → ready = [])

def Spec.Valid (spec : Spec) : Prop := ValidTable spec.table spec.current spec.ready
-- ANCHOR_END: schedulingInvariant

def Spec.mark (spec : Spec) (pid : Pid) (status : Status) : Spec :=
  { spec with table := spec.table.set pid.val { spec.entry pid with status := status } pid.isLt }

-- ANCHOR: schedulerSemantics
inductive Spec.Step : Spec → Event → Reply → Spec → Prop where
  | idle (idle : spec.current = none) : Spec.Step spec event .idle spec
  | yieldAlone (current : spec.current = some pid) (queue : spec.ready = []) :
      Spec.Step spec .yield (.running pid) spec
  | yieldMore (current : spec.current = some pid) (queue : spec.ready = next :: rest) :
      Spec.Step spec .yield (.running next)
        { (spec.mark pid .ready).mark next .running with
          current := some next, ready := rest ++ [pid] }
  | exitLast (current : spec.current = some pid) (queue : spec.ready = []) :
      Spec.Step spec .exit .idle { spec.mark pid .exited with current := none, ready := [] }
  | exitMore (current : spec.current = some pid) (queue : spec.ready = next :: rest) :
      Spec.Step spec .exit (.running next)
        { (spec.mark pid .exited).mark next .running with current := some next, ready := rest }

inductive Spec.Trace : Spec → List Event → List Reply → Spec → Prop where
  | nil : Spec.Trace spec [] [] spec
  | cons (first : Spec.Step before event reply middle)
      (rest : Spec.Trace middle events replies after) :
      Spec.Trace before (event :: events) (reply :: replies) after
-- ANCHOR_END: schedulerSemantics

end Course.CooperativeKernel
