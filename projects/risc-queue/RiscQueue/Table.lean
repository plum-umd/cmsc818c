import RiscQueue.Image
import RiscQueue.Program
import RiscQueue.View

namespace Course.RiscQueue

open Plos.RiscV

-- ANCHOR: ring
/-- Persistent runtime state, with no shadow list of logical queue entries. -/
structure Ring where
  memory : Memory
  capacity : Nat
  head : Nat
  count : Nat
  deriving DecidableEq

namespace Ring

def cells (ring : Ring) : List Word :=
  (List.range ring.capacity).map fun i => BitVec.ofNat 64
    ((ring.memory.load .user .read (256 + BitVec.ofNat 64 (8*i)) .double).toOption.getD 0)

def words (ring : Ring) : List Word :=
  View.words ring.cells ring.head ring.count ring.capacity

def view (ring : Ring) : List Nat := ring.words.map BitVec.toNat

structure Valid (ring : Ring) : Prop where
  headBound : ring.head < ring.capacity
  countBound : ring.count ≤ ring.capacity
  base : ring.memory.base = 0
  size : ring.memory.bytes.size = 256 + 8*ring.capacity
  regions : ring.memory.regions = Image.regions code ring.capacity
  fits : 256 + 8*ring.capacity ≤ 2^64
  popCode : CodeAt ring.memory .user 0 code
  appendCode : Append.Code ring.memory .user 128
  represented : ∃ cells : List Word, cells.length = ring.capacity ∧
    Lookup.Table ring.memory .user 256 cells
-- ANCHOR_END: ring

def padded (values : List Word) (capacity : Nat) : List Word :=
  values ++ List.replicate (capacity-values.length) 0

theorem padded_length (values : List Word) (capacity : Nat) (fits : values.length ≤ capacity) :
    (padded values capacity).length = capacity := by
  simp only [padded, List.length_append, List.length_replicate]
  omega

-- ANCHOR: init
def init (values : List Word) (capacity : Nat) : Ring :=
  ⟨Image.memory code (padded values capacity) capacity, capacity, 0, values.length⟩

theorem init_valid (values : List Word) (capacity : Nat) (positive : 0 < capacity)
    (length : values.length ≤ capacity) (fits : 256 + 8*capacity ≤ 2^64) :
    (init values capacity).Valid :=
  ⟨positive, length, Image.memory_base _ _ _, Image.memory_size _ _ _,
    (by unfold init Image.memory; rfl), fits,
    Image.pop_code _ code_bound _ _, Image.append_code _ code_bound _ _,
    padded values capacity, padded_length _ _ length,
    Image.table _ code_bound _ _ (by rw [padded_length _ _ length]; exact Nat.le_refl _) fits⟩
-- ANCHOR_END: init

@[simp] theorem cells_length (ring : Ring) : ring.cells.length = ring.capacity := by
  simp [cells]

@[simp] theorem words_length (ring : Ring) : ring.words.length = ring.count := by
  simp [words]

@[simp] theorem view_length (ring : Ring) : ring.view.length = ring.count := by
  simp [view]

theorem cells_eq (ring : Ring) (values : List Word) (length : values.length = ring.capacity)
    (table : Lookup.Table ring.memory .user 256 values) : ring.cells = values := by
  apply List.ext_getElem (by simp [cells, length])
  intro i hi hj
  have loaded := table.2 i values[i] (List.getElem?_eq_getElem hj)
  simp only [cells, List.getElem_map, List.getElem_range, loaded]
  change BitVec.ofNat 64 values[i].toNat = values[i]
  simp

theorem table (ring : Ring) (valid : ring.Valid) :
    Lookup.Table ring.memory .user 256 ring.cells := by
  rcases valid.represented with ⟨values, length, represented⟩
  rw [ring.cells_eq values length represented]
  exact represented

theorem init_cells (values : List Word) (capacity : Nat) (length : values.length ≤ capacity)
    (fits : 256 + 8*capacity ≤ 2^64) :
    (init values capacity).cells = padded values capacity :=
  cells_eq _ _ (padded_length _ _ length)
    (Image.table _ code_bound _ _ (by rw [padded_length _ _ length]; exact Nat.le_refl _) fits)

theorem init_words (values : List Word) (capacity : Nat) (length : values.length ≤ capacity)
    (fits : 256 + 8*capacity ≤ 2^64) : (init values capacity).words = values := by
  change View.words _ 0 values.length capacity = values
  rw [init_cells _ _ length fits]
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [View.words, List.getElem_map, List.getElem_range, List.getElem!_toArray]
  rw [show View.slot 0 capacity i = i by simp [View.slot, show i < capacity by omega]]
  rw [getElem!_pos (padded values capacity) i (by rw [padded_length _ _ length]; omega)]
  simp [padded, List.getElem_append_left hj]

theorem slot_address (ring : Ring) (valid : ring.Valid) (index : Nat)
    (inside : index < ring.capacity) :
    (256 + BitVec.ofNat 64 (8*index)).toNat = 256 + 8*index := by
  have := valid.fits
  simp [BitVec.toNat_add, Nat.mod_eq_of_lt (show 256+8*index < 2^64 by omega),
    Nat.mod_eq_of_lt (show 8*index < 2^64 by omega)]

theorem slot_mapped (ring : Ring) (valid : ring.Valid) (index : Nat)
    (inside : index < ring.capacity) (access : Access) (dataAccess : access ≠ .execute) :
    ring.memory.Mapped .user access (256 + BitVec.ofNat 64 (8*index)) 8 := by
  have address := ring.slot_address valid index inside
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [address]; omega
  · rw [valid.base, address]; omega
  · rw [valid.base, valid.size, address]; omega
  · refine ⟨⟨256, 8*ring.capacity, true, true, false, true⟩, ?_, ?_⟩
    · simp [valid.regions, Image.regions]
    · simp only [address]
      refine ⟨by omega, by omega, by have := valid.fits; omega, (by simp), ?_⟩
      cases access <;> simp_all

theorem capacity_fits (ring : Ring) (valid : ring.Valid) : ring.capacity < 2^64 := by
  have := valid.fits
  omega

theorem cell_load (ring : Ring) (valid : ring.Valid) (index : Nat)
    (inside : index < ring.capacity) :
    ring.memory.load .user .read (256 + BitVec.ofNat 64 (8*index)) .double =
      .ok ring.cells[index]!.toNat := by
  have bound : index < ring.cells.length := by simpa using inside
  simpa only [getElem!_pos ring.cells index bound] using
    (ring.table valid).2 index ring.cells[index] (List.getElem?_eq_getElem bound)

end Ring
end Course.RiscQueue
