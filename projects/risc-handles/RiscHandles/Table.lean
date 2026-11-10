import RiscHandles.Image
import RiscHandles.Program
import RiscHandles.Support

namespace Course.RiscHandles

open Plos.RiscV

-- ANCHOR: native
/-- Bytes are authoritative; there is no stored logical list of channels. -/
structure Native where
  memory : Memory
  length : Nat
  capacity : Nat
  deriving DecidableEq

namespace Native

/-- Decode the logical view when needed for specifications, not for native lookup or append. -/
def words (table : Native) : List Word :=
  (List.range table.length).map fun i => BitVec.ofNat 64
    ((table.memory.load .user .read (256 + BitVec.ofNat 64 (8*i)) .double).toOption.getD 0)

/-- A persistent table retains both code images, its layout, and a represented logical sequence. -/
structure Valid (table : Native) : Prop where
  base : table.memory.base = 0
  size : table.memory.bytes.size = 256 + 8*table.capacity
  regions : table.memory.regions = Image.regions code table.capacity
  fits : 256 + 8*table.capacity ≤ 2^64
  length_le : table.length ≤ table.capacity
  codeBound : code.size ≤ 16
  lookupCode : Lookup.Code table.memory .user 0
  appendCode : CodeAt table.memory .user 64 code
  represented : ∃ channels : List Word, channels.length = table.length ∧
    Lookup.Table table.memory .user 256 channels
-- ANCHOR_END: native

-- ANCHOR: init
/-- Load a fresh image once; subsequent operations must retain their execution's memory. -/
def init (channels : List Word) (capacity : Nat) : Native :=
  ⟨Image.memory code channels capacity, channels.length, capacity⟩

theorem init_valid (channels : List Word) (capacity : Nat) (bound : code.size ≤ 16)
    (length : channels.length ≤ capacity) (fits : 256 + 8*capacity ≤ 2^64) :
    (init channels capacity).Valid :=
  ⟨Image.memory_base _ _ _, Image.memory_size _ _ _, (by unfold init Image.memory; rfl),
    fits, length, bound,
    Image.lookup_code _ _ _, Image.append_code _ bound _ _,
    channels, rfl, Image.table _ bound _ _ length fits⟩
-- ANCHOR_END: init

@[simp] theorem words_length (table : Native) : table.words.length = table.length := by
  simp [words]

/-- Successful represented loads make the default in `words` unreachable. -/
theorem words_eq (table : Native) (channels : List Word) (length : channels.length = table.length)
    (represented : Lookup.Table table.memory .user 256 channels) : table.words = channels := by
  apply List.ext_getElem (by simp [words, length])
  intro i hi hj
  have loaded := represented.2 i channels[i] (List.getElem?_eq_getElem hj)
  simp only [words, List.getElem_map, List.getElem_range, loaded]
  change BitVec.ofNat 64 channels[i].toNat = channels[i]
  simp

theorem init_words (channels : List Word) (capacity : Nat) (bound : code.size ≤ 16)
    (length : channels.length ≤ capacity) (fits : 256 + 8*capacity ≤ 2^64) :
    (init channels capacity).words = channels :=
  words_eq _ _ rfl (Image.table _ bound _ _ length fits)

theorem table (native : Native) (valid : native.Valid) :
    Lookup.Table native.memory .user 256 native.words := by
  rcases valid.represented with ⟨channels, length, represented⟩
  rw [native.words_eq channels length represented]
  exact represented

/-- Every capacity slot is readable and writable, not executable. -/
theorem slot_mapped (table : Native) (valid : table.Valid) (index : Nat)
    (inside : index < table.capacity) (access : Access) (dataAccess : access ≠ .execute) :
    table.memory.Mapped .user access (256 + BitVec.ofNat 64 (8*index)) 8 := by
  have address : (256 + BitVec.ofNat 64 (8*index)).toNat = 256 + 8*index := by
    simpa using Support.slot_address 256 table.capacity index valid.fits inside
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [address]; omega
  · rw [valid.base, address]; omega
  · rw [valid.base, valid.size, address]; omega
  · refine ⟨⟨256, 8*table.capacity, true, true, false, true⟩, ?_, ?_⟩
    · simp [valid.regions, Image.regions]
    · simp only [address]
      refine ⟨by omega, by omega, by have := valid.fits; omega, (by simp), ?_⟩
      cases access <;> simp_all

end Native
end Course.RiscHandles
