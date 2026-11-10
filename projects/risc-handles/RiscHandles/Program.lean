import Plos.RiscV.Assembler

namespace Course.RiscHandles

open Plos.RiscV Assembler.Reg

-- ANCHOR: program
/-- Implement bounded append: a0 = buffer, a1 = length, a2 = capacity, a3 = channel.
Return a0 = new length, a1 = success. Only a0, a1, and a4 may change. -/
def program : List Assembler.Item := []

def code : Array InstructionWord :=
  (Assembler.assemble program).toOption.get (by decide +kernel)
-- ANCHOR_END: program

end Course.RiscHandles
