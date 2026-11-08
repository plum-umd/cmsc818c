import ProtectedMemory.Semantics

namespace Course.ProtectedMemory.Examples

-- ANCHOR: exampleMemory
def initial : Memory := {
  base := 0x1000
  bytes := Array.replicate 32 0
  regions := [
    ⟨0x1000, 16, .left, true, true⟩,
    ⟨0x1010, 16, .right, true, true⟩] }
-- ANCHOR_END: exampleMemory

end Course.ProtectedMemory.Examples
