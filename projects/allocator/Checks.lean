import Allocator

open Course.Allocator

private def memory : Memory := ⟨0x1000, Array.replicate 24 0xA5⟩
private def heap : Heap := ⟨memory, 0x1000⟩

-- Checks are executable examples, not proofs of the universally quantified exercise goals.
#guard init memory = some heap
#guard init ⟨3, #[]⟩ = none
#guard init ⟨addressLimit - 8, Array.replicate 16 0⟩ = none
#guard init ⟨0, #[]⟩ = some ⟨⟨0, #[]⟩, 0⟩
#guard allocate heap 0 = (.error .zeroSize, heap)
#guard allocate heap 7 = (.error .unalignedSize, heap)
#guard allocate heap 32 = (.error .outOfMemory, heap)
-- Invalid size takes precedence over exhaustion.
#guard allocate heap 25 = (.error .unalignedSize, heap)
#guard allocate heap 8 = (.allocated ⟨0x1000, 8⟩, { heap with next := 0x1008 })
#guard (allocate heap 8).2.memory.bytes = memory.bytes

private def full : Heap := (allocate heap 24).2
#guard full.next = 0x1018
#guard allocate full 8 = (.error .outOfMemory, full)

-- The last aligned block ends at 2^64. The sentinel must not wrap back to zero.
private def top : Heap := ⟨⟨addressLimit - 8, Array.replicate 8 0⟩, addressLimit - 8⟩
#guard (allocate top 8).1 = .allocated ⟨BitVec.ofNat 64 (addressLimit - 8), 8⟩
#guard (allocate top 8).2.next = addressLimit
#guard allocate (allocate top 8).2 8 = (.error .outOfMemory, (allocate top 8).2)

-- Sequential allocations are adjacent, not overlapping.
#guard (allocate (allocate heap 8).2 16).1 = .allocated ⟨0x1008, 16⟩
