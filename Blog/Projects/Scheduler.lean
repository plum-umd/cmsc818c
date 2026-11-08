import VersoBlog
import CooperativeKernel
import CooperativeKernel.Examples

open Verso Genre Blog
open Verso.Code.External

set_option verso.exampleProject "."

#doc (Page) "Project 6: A Cooperative Scheduler" =>

How can several computations make progress while sharing one CPU? A scheduler must preserve
each computation while changing which one runs. A valid ready queue alone is insufficient:
restoring the wrong PC or register file could resume a different computation, and restoring
the wrong protection domain could give it another process's authority.

This project specifies a small cooperative scheduler, implements context management, and
connects the two with a simulation theorem. The
[starter source](https://github.com/plum-umd/cmsc818c/tree/main/projects/scheduler) uses supplied
machine contexts and protection-domain types. No earlier project solution is required.

# Build and Explore

From the repository root:

```
cd projects/scheduler
lake build
```

The main modules are:

- `CooperativeKernel/Spec.lean`: processes, scheduler invariants, and an abstract event semantics.
- `CooperativeKernel/Kernel.lean`: the live CPU, parked contexts, abstraction function,
  and concrete event handler.
- `CooperativeKernel/Exercises.lean`: simulation, framing, restoration, and lifecycle obligations.
- `CooperativeKernel/Examples.lean` and `Checks.lean`: configurations and execution checks.

The starter builds and the examples execute. The universal exercise propositions remain
proof obligations for students.

# Specify the Scheduler's View of Processes

```anchor processModel (module := CooperativeKernel.Spec)
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
```

The model fixes three process identifiers. Every process has a context containing its full
register file and PC, a protection domain, and a status. The abstract table always records
the process's latest context, including for the current process. `current` is absent only
when the system has become idle; `ready` lists runnable processes in scheduling order.

Process identity and protection domain are different concepts. Several processes may share
a domain. The scheduler must select the chosen process's assigned domain, not infer authority
from its PID or assume a one-to-one correspondence.

`yield` and `exit` are explicit kernel events with no caller-PID parameter. The current process
is the one yielding or exiting. Replies describe the process selected to run next, or an idle
system; they are observations for the host, not return values delivered immediately to the
process that yielded.

## State the Scheduling Invariant

```anchor schedulingInvariant (module := CooperativeKernel.Spec)
def ValidTable (table : Vector Process 3) (current : Option Pid) (ready : List Pid) : Prop :=
  ready.Nodup ∧
  (∀ pid : Pid, (table[pid.val]).status = .running ↔ current = some pid) ∧
  (∀ pid : Pid, pid ∈ ready ↔ (table[pid.val]).status = .ready) ∧
  (current = none → ready = [])

def Spec.Valid (spec : Spec) : Prop := ValidTable spec.table spec.current spec.ready
```

Read each clause as a statement about agreement between representations:

- The ready queue has no duplicates.
- A process is marked running exactly when it is the current process.
- A process occurs in the ready queue exactly when it is marked ready.
- If there is no current process, the ready queue is empty.

Together these imply that the current process is not also queued and exited processes are
neither queued nor running. Since the model has no blocked status, a valid idle system has
only exited processes. A single remaining process may be current with an empty ready queue.

The process table retains exited entries and their final contexts. There is no creation or
PID reuse in the core project, so those identities cannot become runnable again.

## Describe Permitted Events

`Spec.mark` changes only a process's status. Contexts, domains, and memory are unchanged.
The event rules state who runs next and how the queue changes:

```anchor schedulerSemantics (module := CooperativeKernel.Spec)
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
```

Yield appends the current process behind the processes already waiting, then selects the
head. If nobody else is waiting, the same process continues. Exit marks the current process
exited without enqueuing it. If nobody remains ready, the system becomes idle.

The abstract rules do not copy registers: the latest context is already in the abstract table.
Students will first prove that these rules preserve validity, determine a unique result,
and preserve every process context, domain assignment, and memory byte.

# Implement Live and Parked Contexts

```anchor kernelState (module := CooperativeKernel.Kernel)
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
```

The concrete representation separates the CPU from the parked table. For the current process,
the live context is `cpu`; its table entry may be stale because the process has executed since
it was last restored. For every other process, the table entry is authoritative.

The abstraction function `view` overlays the live CPU context onto the current process's entry.
It does not replace that process's identity, domain, or status. The supplied lemma makes the
key observation explicit:

```anchor viewCurrent (module := CooperativeKernel.Kernel)
theorem view_current (kernel : Kernel) (pid : Pid) (current : kernel.current = some pid) :
    ((view kernel).entry pid).context = kernel.cpu := by
  simp [view, Spec.entry, current]
```

`Kernel.Valid` additionally requires `activeDomain` to agree with the current process's assigned
domain, or to be absent when the system is idle. `Rep` combines this concrete invariant with
equality to the abstract scheduler state.

Requiring the current parked snapshot to equal `cpu` would be the wrong invariant: it would
exclude the ordinary case where a process has advanced its PC or changed its registers.

## Save, Select, and Restore

```anchor switchImplementation (module := CooperativeKernel.Kernel)
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
```

`archive` copies the complete live context into the outgoing process's slot and changes its
status. `select` removes the next ready PID, marks it running, restores its context, and selects
its domain. With no ready process, it clears the current PID and active domain and clears the
live CPU record. The archived process contexts remain in the table.

Yield saves the outgoing process as ready, appends it to the ready list, and selects again.
Exit archives the final context as exited and selects without appending. Saving must precede
restoration: otherwise the outgoing process could receive the incoming process's registers.

Each handler invocation is an atomic kernel event in this model. Its helpers may construct
intermediate records that do not satisfy the final scheduling invariant. No guest execution or
interrupt can observe those intermediate records here. Interruptible context switching would
require additional invariants and a richer execution model.

# Begin with a Stale Parked Snapshot

The example uses distinct register patterns and PCs for each context. Processes 0 and 2 share
the left domain; process 1 uses the right domain. The current process's live context deliberately
differs from its parked snapshot:

```anchor initialKernel (module := CooperativeKernel.Examples)
def initial : Kernel := {
  table := Vector.ofFn fun pid => {
    context := context (pid.val + 1)
    domain := if pid.val = 1 then .right else .left
    status := if pid.val = 0 then .running else .ready }
  current := some 0
  ready := [1, 2]
  cpu := context 10
  activeDomain := some .left
  memory := Course.ProtectedMemory.Examples.initial }
```

```leanInit schedulerProject
```

```lean schedulerProject
open Course.CooperativeKernel Course.CooperativeKernel.Examples

example : (initial.entry 0).context ≠ initial.cpu := by decide
example : ((view initial).entry 0).context = initial.cpu := by decide

example :
    let result := runEvents initial [.yield, .yield, .yield]
    result.1 = [.running 1, .running 2, .running 0] ∧
      result.2.cpu = initial.cpu ∧ result.2.activeDomain = some .left := by decide
```

After three yields, process 0 must resume its live computation, not the stale table entry with
which it began. Comparing complete contexts checks the PC and all backing register slots.

```lean schedulerProject
example :
    let final := (runEvents initial [.exit, .exit, .exit]).2
    final.current = none ∧ final.ready = [] ∧ final.activeDomain = none ∧
      final.memory = initial.memory := by decide
```

Exiting the last process leaves an idle system without changing memory. Further yield and exit
events return `idle` and leave that state unchanged.

# The Simulation and Frame Goals

```anchor contextSimulation (module := CooperativeKernel.Exercises)
def Simulation : Prop :=
  ∀ (spec : Spec) (kernel : Kernel) (event : Event), Rep spec kernel →
    ∃ nextSpec : Spec,
      Spec.Step spec event (handle kernel event).1 nextSpec ∧
      Rep nextSpec (handle kernel event).2
```

Every event handled by the concrete kernel must produce an abstractly permitted reply and
next state, and that next state must again be represented by the concrete result. Proving
only that the ready list remains well formed would leave the context and authority obligations
unresolved.

```anchor switchFrame (module := CooperativeKernel.Exercises)
def SwitchFrame : Prop :=
  ∀ (kernel : Kernel) (event : Event), kernel.Valid →
    let next := (handle kernel event).2
    next.memory = kernel.memory ∧
      ∀ pid : Pid,
        ((view next).entry pid).context = ((view kernel).entry pid).context ∧
        ((view next).entry pid).domain = ((view kernel).entry pid).domain
```

The frame compares *logical* process contexts, through `view`, rather than raw table entries.
Raw entries are expected to change when a live context is archived. The theorem says that
switching changes neither the computation represented for any PID nor its domain assignment,
and changes no memory. Only scheduling status and ownership of the live CPU change.

Even an exiting process retains its final snapshot in this model. No instruction execution
occurs during these event traces, so the context-frame statement applies to every PID.
When adding guest execution between events, the running process's computation will advance;
the switch itself must still preserve the state at which that event began.

`Exercises.Restoration` makes the selected-process obligation explicit: the returned PID must
be current, the CPU must contain its pre-switch logical context, and the active domain must
be that process's assigned domain. This rules out restoring the right register file with the
wrong PC, using a stale snapshot, or retaining the outgoing process's domain.

# Preserve Process Lifecycle Across Traces

```anchor noResurrection (module := CooperativeKernel.Exercises)
def NoResurrection : Prop :=
  ∀ (kernel : Kernel) (events : List Event) (pid : Pid), kernel.Valid →
    ((view kernel).entry pid).status = .exited →
      let final := (runEvents kernel events).2
      ((view final).entry pid).status = .exited ∧
      final.current ≠ some pid ∧ pid ∉ final.ready
```

This theorem begins with a process already exited. After any finite event list, it must still
be exited, absent from the ready queue, and not current. Combine it with the exit rule to show
that a process never runs again after it exits during a trace.

`Exercises.TraceSimulation` extends the one-event simulation to event sequences. Its induction
must carry the representation relation, which supplies the next call's scheduler and
active-domain invariants. Do not assume that each call starts in a freshly initialized state.

# Core Assignment

1. *Understand valid scheduling states.* Prove `Exercises.SchedulingFacts` and establish
   validity of the example. Explain why a current process cannot also appear in `ready`,
   and why idle implies all processes have exited in this particular model.
2. *Prove the abstract rules correct.* Prove `Exercises.SpecPreservation`,
   `Exercises.SpecDeterminism`, and `Exercises.SpecFrame`. For yield with waiting processes,
   identify the facts that justify appending the outgoing PID without introducing a duplicate.
3. *Connect live and parked representations.* Establish how `view` reads current and inactive
   entries. Prove `Exercises.Simulation`, including the single-process yield and final exit
   cases. Do not strengthen the precondition to require a fresh current table snapshot.
4. *Recover the concrete guarantees.* Derive `Exercises.Preservation`,
   `Exercises.SwitchFrame`, `Exercises.Restoration`, and `Exercises.IdleCorrect`. Explain
   which results follow through simulation and the abstract frame, rather than repeating a
   low-level case analysis of the event handler.
5. *Compose events and prove lifecycle safety.* Prove `Exercises.TraceSimulation` and
   `Exercises.NoResurrection`. Derive memory preservation across the trace and explain why
   the representation relation remains usable after saving and restoring several processes.

Create `CooperativeKernel/Solution.lean` and import it from `Checks.lean`. Keep the supplied
definitions and exercise propositions fixed. Add tests in which the live CPU differs from the
current parked snapshot, domains change during a switch, one process remains, and every
process exits. Tests should compare PCs as well as registers and inspect queue contents.

Submit proofs with an explanation of the abstraction function, the authoritative location
of a process's context, and the atomic-event assumption. Describe a plausible context-switch
bug that preserves the queue invariant but violates simulation. Audit theorem assumptions
using `#print axioms`, as demonstrated in `Audit.lean`; do not introduce new axioms or proof
placeholders. Ask an agent to explain whose state each table entry and CPU field represents
at each phase before proposing the save-and-restore proof.

# Optional Extensions

1. *Round-robin selection.* State and prove a bound on selection under a finite sequence of
   yield events with a fixed runnable set. State the cooperation assumption: no scheduler
   theorem can force a process that never yields to relinquish the CPU in this model.
2. *Change the ready-queue representation.* Replace the list with a circular buffer and
   prove scheduler refinement. Account for PID uniqueness and the temporary capacity needed
   when enqueueing the current process before selecting the next one. A FIFO contract alone
   does not establish the scheduler's lifecycle invariant.
3. *Connect guest execution and protected access.* Run instructions using the live CPU and
   use the active domain when invoking the protected-memory service. State and prove the
   resulting combined invariant. Kernel switching preserves all bytes here; that fact alone
   is not a proof about memory writes performed by guest instructions.
4. *Add system-call entry.* Connect yield and exit to a distinguished machine event. Specify
   the continuation PC and advance it where required by the calling convention. Do not
   interpret every machine fault as a successful yield or repeatedly resume at a serviced
   request instruction.

# Scope

The fixed process set, explicit events, and atomic handlers leave out creation, PID reuse,
blocking communication, asynchronous interrupts, and multicore execution. Process domains
are metadata that the model selects correctly; establishing physical enforcement of those
permissions requires the machine and protection integration described above.

This project prepares the reasoning needed for a small kernel: preserve computations while
moving their representations, maintain resource ownership, and compose guarantees across
state transitions. It does not claim to implement a complete operating system.
