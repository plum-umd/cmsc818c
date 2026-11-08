import CooperativeKernel.Kernel
import ProtectedMemory.Examples

namespace Course.CooperativeKernel.Examples

def context (seed : Nat) : Context := {
  registers := Vector.ofFn fun register => BitVec.ofNat 64 (100 * seed + register.val)
  pc := BitVec.ofNat 64 (16 * seed) }

-- ANCHOR: initialKernel
def initial : Kernel := {
  table := Vector.ofFn fun pid => {
    context := context (pid.val + 1)
    domain := if pid.val = 1 then .right else .left
    status := if pid.val = 0 then .running else .ready }
  current := some 0
  ready := [1, 2]
  cpu := context 10
  activeDomain := some .left
  memory := Course.ProtectedMemory.Examples.initial }
-- ANCHOR_END: initialKernel

end Course.CooperativeKernel.Examples
