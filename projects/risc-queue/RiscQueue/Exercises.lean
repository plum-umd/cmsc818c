import RiscQueue.Policy
import RiscQueue.Support

namespace Course.RiscQueue.Exercises

open Plos.RiscV

-- ANCHOR: viewLaws
def ViewPop : Prop :=
  ∀ (cells : List Word) (head count capacity : Nat), head < capacity → count < capacity →
    View.words cells head (count+1) capacity =
      cells[head]! :: View.words cells (nextHead head capacity) count capacity

def ViewPush : Prop :=
  ∀ (cells : List Word) (head count capacity : Nat) (value : Word),
    cells.length = capacity → head < capacity → count < capacity →
      View.words (cells.set (View.slot head capacity count) value) head (count+1) capacity =
        View.words cells head count capacity ++ [value]
-- ANCHOR_END: viewLaws

-- ANCHOR: runCorrect
def RunCorrect : Prop :=
  ∀ (state : State) (base ret address value : Word) (head count capacity fuel : Nat),
    Inputs code state base ret address value head count capacity → 16 ≤ fuel →
      Correct head count capacity value ret state (resumeCall ret fuel state)
-- ANCHOR_END: runCorrect

def CallCorrect : Prop :=
  ∀ (call : Call) (original prepared : State) (address value : Word)
    (head count capacity fuel : Nat),
    call.prepare original = .ok prepared →
    Inputs code prepared call.entry call.returnAddress address value head count capacity →
    16 ≤ fuel → ∃ result, callRoutine call fuel original = .ok result ∧
      Correct head count capacity value call.returnAddress prepared result

-- ANCHOR: nativeLaws
def NativePopCorrect : Prop :=
  ∀ ring : Ring, ring.Valid → 0 < ring.count → PopCorrect ring

def NativePushCorrect : Prop :=
  ∀ (ring : Ring) (value : Word), ring.Valid → ring.count < ring.capacity →
    PushCorrect ring value
-- ANCHOR_END: nativeLaws

-- ANCHOR: policyLaws
def AdmissionCorrect : Prop := ∀ pids : List Nat, Policy.view (Policy.fromList pids) = pids

def PolicyCorrect : Prop :=
  ∀ correct : CorrectRing,
    (∀ (queue : Policy.Queue) (pid : Nat),
      Policy.view (Policy.enqueue correct queue pid) =
        (Plos.Kernel.RunQueue.enqueue ⟨Policy.view queue⟩ pid).pids) ∧
    (∀ queue : Policy.Queue,
      (Policy.dequeue correct queue).map (fun (pid, rest) => (pid, Policy.view rest)) =
        (Policy.view queue).head?.map (fun pid => (pid, (Policy.view queue).tail))) ∧
    (∀ (queue : Policy.Queue) (pid : Nat),
      Policy.view (Policy.remove queue pid) =
        (Policy.view queue).filter (fun p => decide (p ≠ pid))) ∧
    (∀ queue : Policy.Queue, Policy.isEmpty queue = (Policy.view queue).isEmpty)

def KernelContract : Prop :=
  ∀ correct : CorrectRing,
    ∃ contract : Plos.Kernel.Components.QueueContract (Policy.ops correct),
      contract.view = Policy.view
-- ANCHOR_END: policyLaws

-- ANCHOR: nativeUse
def NativeUse : Prop :=
  ∀ correct : CorrectRing,
    (∀ (queue : Policy.Queue) (pid : Nat),
      Plos.Kernel.RunQueue.contains ⟨Policy.view queue⟩ pid = true →
        Policy.enqueue correct queue pid = queue) ∧
    (∀ (ring : Ring) (valid : ring.Valid) (pid : Nat),
      Plos.Kernel.RunQueue.contains ⟨ring.view⟩ pid = false →
      ∀ (room : ring.count < ring.capacity), pid < 2^64 →
        Policy.enqueue correct (.native ring valid) pid =
          .native (ring.push (BitVec.ofNat 64 pid)) (correct.push ring _ valid room).valid) ∧
    (∀ (ring : Ring) (valid : ring.Valid) (nonempty : 0 < ring.count),
      Policy.dequeue correct (.native ring valid) =
        some (ring.pop.1.toNat, .native ring.pop.2 (correct.pop ring valid nonempty).valid))

/-- Exhibit the completed ring proof and its concrete kernel contract; do not assume the API. -/
def Integrated : Prop :=
  ∃ correct : CorrectRing,
    ∃ contract : Plos.Kernel.Components.QueueContract (Policy.ops correct),
      contract.view = Policy.view
-- ANCHOR_END: nativeUse

end Course.RiscQueue.Exercises
