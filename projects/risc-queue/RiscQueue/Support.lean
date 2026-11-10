import RiscQueue.Spec

namespace Course.RiscQueue.Support

open Plos.RiscV

theorem not_return {memory : Memory} {mode : Mode} {base ret : Word}
    {code : Array InstructionWord} (image : CodeAt memory mode base code)
    (location : ReturnAt base ret code) (offset : Nat) (inside : offset < 4 * code.size) :
    base + BitVec.ofNat 64 offset ≠ ret := by
  have address := image.address offset inside
  intro same
  rw [same] at address
  have := location.outside
  omega

end Course.RiscQueue.Support
