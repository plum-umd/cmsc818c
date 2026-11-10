import RiscQueue.Table

namespace Course.RiscQueue.Ring

open Plos.RiscV

def popCall (ring : Ring) : Call := {
  entry := 0, returnAddress := 192, stackPointer := 0
  arguments := fun i => if i.val = 0 then 256
    else if i.val = 1 then BitVec.ofNat 64 ring.head
    else if i.val = 2 then BitVec.ofNat 64 ring.count
    else if i.val = 3 then BitVec.ofNat 64 ring.capacity else 0 }

def writeCall (ring : Ring) (index : Nat) (value : Word) : Call :=
  Append.invocation 256 (BitVec.ofNat 64 index) (BitVec.ofNat 64 ring.capacity) value 0 128 192

end Course.RiscQueue.Ring
