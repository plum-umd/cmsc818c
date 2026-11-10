import Plos.RiscV.Assembler

namespace Course.RiscLookup

open Plos.RiscV
open Assembler.Reg

-- ANCHOR: starter
/-- Replace the empty body with your assembly program. a0 = table, a1 = length, a2 = index.
Return through ra with a0 = value (zero on a miss), a1 = found. Only a0–a2 may change. -/
def program : List Assembler.Item := []

/-- Assembly must succeed by proof; do not replace errors with an empty image. -/
def code : Array InstructionWord :=
  (Assembler.assemble program).toOption.get (by decide +kernel)
-- ANCHOR_END: starter

end Course.RiscLookup
