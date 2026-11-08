import Allocator.Machine

namespace Course.Allocator

/-- `next` is an absolute, mathematical address, including the one-past-the-end sentinel. -/
structure Heap where
  memory : Memory
  next : Nat
  deriving DecidableEq, Repr

def Heap.Valid (heap : Heap) : Prop :=
  heap.memory.base % wordBytes = 0 ∧
  heap.next % wordBytes = 0 ∧
  heap.memory.base ≤ heap.next ∧
  heap.next ≤ heap.memory.finish ∧
  heap.memory.finish ≤ addressLimit

/-- Construct an empty allocation history over caller-supplied bytes. -/
def init (memory : Memory) : Option Heap :=
  if memory.base % wordBytes = 0 ∧ memory.finish ≤ addressLimit then
    some ⟨memory, memory.base⟩
  else none

inductive Error where
  | zeroSize
  | unalignedSize
  | outOfMemory
  deriving DecidableEq, Repr

inductive Reply where
  | allocated (block : Block)
  | error (reason : Error)
  deriving DecidableEq, Repr

/-- Allocate positive multiples of eight bytes. Allocation neither clears nor writes payload. -/
def allocate (heap : Heap) (request : Word) : Reply × Heap :=
  let size := request.toNat
  if size = 0 then (.error .zeroSize, heap)
  else if size % wordBytes ≠ 0 then (.error .unalignedSize, heap)
  else if heap.next + size ≤ heap.memory.finish then
    (.allocated ⟨BitVec.ofNat 64 heap.next, size⟩, { heap with next := heap.next + size })
  else (.error .outOfMemory, heap)

/-- The request and pre-state determine the reply and next state independently of `allocate`. -/
inductive Step (heap : Heap) (request : Word) : Reply → Heap → Prop where
  | zero (empty : request.toNat = 0) : Step heap request (.error .zeroSize) heap
  | unaligned (positive : request.toNat ≠ 0) (bad : request.toNat % wordBytes ≠ 0) :
      Step heap request (.error .unalignedSize) heap
  | full (positive : request.toNat ≠ 0) (aligned : request.toNat % wordBytes = 0)
      (full : heap.memory.finish < heap.next + request.toNat) :
      Step heap request (.error .outOfMemory) heap
  | success (positive : request.toNat ≠ 0) (aligned : request.toNat % wordBytes = 0)
      (room : heap.next + request.toNat ≤ heap.memory.finish) :
      Step heap request (.allocated ⟨BitVec.ofNat 64 heap.next, request.toNat⟩)
        { heap with next := heap.next + request.toNat }

theorem init_valid (memory : Memory) (heap : Heap) (result : init memory = some heap) :
    heap.Valid := by
  unfold init at result
  split at result
  · next h =>
      cases result
      simp only [Heap.Valid]
      exact ⟨h.1, h.1, Nat.le_refl _, by simp [Memory.finish], h.2⟩
  · contradiction

/-- A supplied baseline: allocation preserves the entire payload, including unallocated bytes. -/
theorem allocate_memory (heap : Heap) (request : Word) :
    (allocate heap request).2.memory = heap.memory := by
  unfold allocate
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

end Course.Allocator
