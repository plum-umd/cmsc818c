import RiscLookup.Spec

namespace Course.RiscLookup.Support

open Plos.RiscV

/-- Fetch and decode one chosen instruction from an installed image. -/
theorem step_at {memory : Memory} {mode : Mode} {base : Word}
    {code : Array InstructionWord} (image : CodeAt memory mode base code)
    (state : State) (mem : state.memory = memory) (privilege : state.mode = mode)
    (i : Fin code.size) (instruction : Instruction)
    (decoded : decode code[i.val] = .ok instruction) :
    step { state with pc := base + BitVec.ofNat 64 (4 * i.val) } =
      execute { state with pc := base + BitVec.ofNat 64 (4 * i.val) } instruction :=
  image.step state mem privilege i instruction decoded

/-- An address inside the code image cannot be the return marker. -/
theorem not_return {memory : Memory} {mode : Mode} {base ret : Word}
    {code : Array InstructionWord} (image : CodeAt memory mode base code)
    (location : ReturnAt base ret code) (offset : Nat) (inside : offset < 4 * code.size) :
    base + BitVec.ofNat 64 offset ≠ ret := by
  have address := image.address offset inside
  intro same
  rw [same] at address
  have := location.outside
  omega

end Course.RiscLookup.Support
