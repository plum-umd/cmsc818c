import Queue.Buffer

namespace Course.Queue.Exercises

-- These propositions state student obligations. They are not assumed theorems.

def Initialization : Prop :=
  ∀ (capacity : Nat), 0 < capacity → Buffer.Rep capacity (Buffer.empty capacity) []

def OccupiedReads : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (i : Nat), Buffer.Valid capacity buffer →
    i < buffer.count → (buffer.head + i) % buffer.slots.size < buffer.slots.size

def Preservation : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (command : Command),
    Buffer.Valid capacity buffer → Buffer.Valid capacity (Buffer.run buffer command).2

-- ANCHOR: queueRefinement
def Refinement : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (command : Command),
    Buffer.Valid capacity buffer →
      ((Buffer.run buffer command).1, Buffer.view (Buffer.run buffer command).2) =
        run capacity (Buffer.view buffer) command
-- ANCHOR_END: queueRefinement

-- ANCHOR: queueSimulation
def Simulation : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (queue : List Word) (command : Command),
    Buffer.Rep capacity buffer queue →
      ∃ nextQueue : List Word,
        Step capacity queue command (Buffer.run buffer command).1 nextQueue ∧
        Buffer.Rep capacity (Buffer.run buffer command).2 nextQueue
-- ANCHOR_END: queueSimulation

-- ANCHOR: queueSimulationTransfer
def SimulationFromRefinement : Prop :=
  Preservation → Refinement → Simulation
-- ANCHOR_END: queueSimulationTransfer

def FailureAtomicity : Prop :=
  ∀ (buffer next : Buffer.State) (command : Command) (reply : Reply),
    Buffer.run buffer command = (reply, next) →
    (reply = .full ∨ reply = .empty) → next = buffer

def PopFrame : Prop :=
  ∀ (buffer : Buffer.State), (Buffer.pop buffer).2.slots = buffer.slots

def TraceRefinement : Prop :=
  ∀ (capacity : Nat) (buffer : Buffer.State) (commands : List Command),
    Buffer.Valid capacity buffer →
      Buffer.Valid capacity (Buffer.runTrace buffer commands).2 ∧
      ((Buffer.runTrace buffer commands).1, Buffer.view (Buffer.runTrace buffer commands).2) =
        Buffer.referenceTrace capacity (Buffer.view buffer) commands

end Course.Queue.Exercises
