import Allocator.Basic

namespace Course.Allocator.Exercises

-- These are specifications to prove, not axioms or declarations of completed theorems.
-- Add your proofs in a new module and import that module from Checks.lean.

def Soundness : Prop :=
  ∀ (heap : Heap) (request : Word), heap.Valid →
    Step heap request (allocate heap request).1 (allocate heap request).2

def Completeness : Prop :=
  ∀ (heap : Heap) (request : Word) (reply : Reply) (next : Heap),
    Step heap request reply next → allocate heap request = (reply, next)

-- ANCHOR: preservation
def Preservation : Prop :=
  ∀ (heap : Heap) (request : Word), heap.Valid → (allocate heap request).2.Valid
-- ANCHOR_END: preservation

-- ANCHOR: stepPreservation
def StepPreservation : Prop :=
  ∀ (heap : Heap) (request : Word) (reply : Reply) (next : Heap),
    heap.Valid → Step heap request reply next → next.Valid
-- ANCHOR_END: stepPreservation

-- ANCHOR: equivalence
def Equivalence : Prop :=
  ∀ (heap : Heap) (request : Word) (reply : Reply) (next : Heap), heap.Valid →
    (Step heap request reply next ↔ allocate heap request = (reply, next))
-- ANCHOR_END: equivalence

-- ANCHOR: preservationViaSpec
def PreservationViaSpec : Prop :=
  Soundness → StepPreservation → Preservation
-- ANCHOR_END: preservationViaSpec

def FailureAtomicity : Prop :=
  ∀ (heap : Heap) (request : Word) (reason : Error) (next : Heap),
    allocate heap request = (.error reason, next) → next = heap

def SuccessContract : Prop :=
  ∀ (heap : Heap) (request : Word) (block : Block) (next : Heap), heap.Valid →
    allocate heap request = (.allocated block, next) →
      block.start.toNat = heap.next ∧
      block.start.toNat % wordBytes = 0 ∧
      block.size = request.toNat ∧ 0 < block.size ∧
      heap.memory.base ≤ block.start.toNat ∧ block.finish ≤ heap.memory.finish ∧
      next.next = block.finish ∧ heap.next < next.next

def Freshness : Prop :=
  ∀ (heap : Heap) (request : Word) (old block : Block) (next : Heap), heap.Valid →
    old.finish ≤ heap.next → allocate heap request = (.allocated block, next) →
      old.Disjoint block

def ConsecutiveDisjointness : Prop :=
  ∀ (heap middle final : Heap) (firstRequest secondRequest : Word) (first second : Block),
    heap.Valid → allocate heap firstRequest = (.allocated first, middle) →
    allocate middle secondRequest = (.allocated second, final) → first.Disjoint second

end Course.Allocator.Exercises
