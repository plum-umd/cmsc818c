import CooperativeKernel.Spec

namespace Course.CooperativeKernel

-- ANCHOR: kernelState
structure Kernel where
  table : Vector Process 3
  current : Option Pid
  ready : List Pid
  cpu : Context
  activeDomain : Option Domain
  memory : Memory
  deriving DecidableEq, Repr

def Kernel.entry (kernel : Kernel) (pid : Pid) : Process := kernel.table[pid.val]

def view (kernel : Kernel) : Spec := {
  table := Vector.ofFn fun pid =>
    if kernel.current = some pid then { kernel.entry pid with context := kernel.cpu }
    else kernel.entry pid
  current := kernel.current
  ready := kernel.ready
  memory := kernel.memory }

def Kernel.Valid (kernel : Kernel) : Prop :=
  (view kernel).Valid ∧
    kernel.activeDomain = kernel.current.map (fun pid => (kernel.entry pid).domain)

def Rep (spec : Spec) (kernel : Kernel) : Prop := kernel.Valid ∧ view kernel = spec
-- ANCHOR_END: kernelState

-- ANCHOR: switchImplementation
def archive (kernel : Kernel) (pid : Pid) (status : Status) : Kernel :=
  let saved := { kernel.entry pid with context := kernel.cpu, status := status }
  { kernel with table := kernel.table.set pid.val saved pid.isLt }

def select (kernel : Kernel) : Reply × Kernel :=
  match kernel.ready with
  | [] => (.idle, { kernel with current := none, cpu := {}, activeDomain := none })
  | pid :: rest =>
      let process := kernel.entry pid
      (.running pid, { kernel with
        table := kernel.table.set pid.val { process with status := .running } pid.isLt
        current := some pid
        ready := rest
        cpu := process.context
        activeDomain := some process.domain })

def handle (kernel : Kernel) (event : Event) : Reply × Kernel :=
  match kernel.current with
  | none => (.idle, kernel)
  | some pid =>
      match event with
      | .yield => select { archive kernel pid .ready with ready := kernel.ready ++ [pid] }
      | .exit => select (archive kernel pid .exited)

def runEvents (kernel : Kernel) : List Event → List Reply × Kernel
  | [] => ([], kernel)
  | event :: events =>
      let (reply, next) := handle kernel event
      let (replies, final) := runEvents next events
      (reply :: replies, final)
-- ANCHOR_END: switchImplementation

-- ANCHOR: viewCurrent
theorem view_current (kernel : Kernel) (pid : Pid) (current : kernel.current = some pid) :
    ((view kernel).entry pid).context = kernel.cpu := by
  simp [view, Spec.entry, current]
-- ANCHOR_END: viewCurrent

end Course.CooperativeKernel
