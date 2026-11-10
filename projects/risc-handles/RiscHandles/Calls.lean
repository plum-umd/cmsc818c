import RiscHandles.Table

namespace Course.RiscHandles.Native

open Plos.RiscV

def appendCall (table : Native) (channel : Word) : Call := {
  entry := 64, returnAddress := 192, stackPointer := 0
  arguments := fun i => if i.val = 0 then 256
    else if i.val = 1 then BitVec.ofNat 64 table.length
    else if i.val = 2 then BitVec.ofNat 64 table.capacity
    else if i.val = 3 then channel else 0 }

def lookupCall (table : Native) (index : Nat) : Call :=
  Lookup.invocation 256 (BitVec.ofNat 64 table.length) (BitVec.ofNat 64 index) 0

end Course.RiscHandles.Native
