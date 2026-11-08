import CooperativeKernel.Kernel

namespace Course.CooperativeKernel.Exercises

def SchedulingFacts : Prop :=
  ∀ spec : Spec, spec.Valid →
    (∀ pid : Pid, spec.current = some pid → pid ∉ spec.ready) ∧
    (spec.current = none → ∀ pid : Pid, (spec.entry pid).status = .exited)

def SpecPreservation : Prop :=
  ∀ (before after : Spec) (event : Event) (reply : Reply), before.Valid →
    Spec.Step before event reply after → after.Valid

def SpecDeterminism : Prop :=
  ∀ (before first second : Spec) (event : Event) (reply₁ reply₂ : Reply), before.Valid →
    Spec.Step before event reply₁ first → Spec.Step before event reply₂ second →
      reply₁ = reply₂ ∧ first = second

def SpecFrame : Prop :=
  ∀ (before after : Spec) (event : Event) (reply : Reply), Spec.Step before event reply after →
    after.memory = before.memory ∧
      ∀ pid : Pid, (after.entry pid).context = (before.entry pid).context ∧
        (after.entry pid).domain = (before.entry pid).domain

-- ANCHOR: contextSimulation
def Simulation : Prop :=
  ∀ (spec : Spec) (kernel : Kernel) (event : Event), Rep spec kernel →
    ∃ nextSpec : Spec,
      Spec.Step spec event (handle kernel event).1 nextSpec ∧
      Rep nextSpec (handle kernel event).2
-- ANCHOR_END: contextSimulation

def Preservation : Prop :=
  ∀ (kernel : Kernel) (event : Event), kernel.Valid → (handle kernel event).2.Valid

-- ANCHOR: switchFrame
def SwitchFrame : Prop :=
  ∀ (kernel : Kernel) (event : Event), kernel.Valid →
    let next := (handle kernel event).2
    next.memory = kernel.memory ∧
      ∀ pid : Pid,
        ((view next).entry pid).context = ((view kernel).entry pid).context ∧
        ((view next).entry pid).domain = ((view kernel).entry pid).domain
-- ANCHOR_END: switchFrame

def Restoration : Prop :=
  ∀ (kernel : Kernel) (event : Event) (pid : Pid), kernel.Valid →
    (handle kernel event).1 = .running pid →
      let next := (handle kernel event).2
      next.current = some pid ∧ next.cpu = ((view kernel).entry pid).context ∧
        next.activeDomain = some (((view kernel).entry pid).domain)

def IdleCorrect : Prop :=
  ∀ (kernel : Kernel) (event : Event), kernel.Valid → kernel.current = none →
    handle kernel event = (.idle, kernel)

def TraceSimulation : Prop :=
  ∀ (spec : Spec) (kernel : Kernel) (events : List Event), Rep spec kernel →
    ∃ nextSpec : Spec,
      Spec.Trace spec events (runEvents kernel events).1 nextSpec ∧
      Rep nextSpec (runEvents kernel events).2

-- ANCHOR: noResurrection
def NoResurrection : Prop :=
  ∀ (kernel : Kernel) (events : List Event) (pid : Pid), kernel.Valid →
    ((view kernel).entry pid).status = .exited →
      let final := (runEvents kernel events).2
      ((view final).entry pid).status = .exited ∧
      final.current ≠ some pid ∧ pid ∉ final.ready
-- ANCHOR_END: noResurrection

end Course.CooperativeKernel.Exercises
