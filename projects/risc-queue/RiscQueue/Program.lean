import Plos.RiscV.Assembler

namespace Course.RiscQueue

open Plos.RiscV Assembler.Reg

-- ANCHOR: program
/-- Implement dequeue: a0 = buffer, a1 = head, a2 = count, a3 = capacity.
Return a0 = value (zero if empty), a1 = new head, a2 = new count, a3 = found.
Only a0–a4 may change. Empty dequeue must not access the data buffer. -/
def program : List Assembler.Item := []

def code : Array InstructionWord :=
  (Assembler.assemble program).toOption.get (by decide +kernel)

/-- The supplied persistent layout reserves 24 words for dequeue. -/
theorem code_bound : code.size ≤ 24 := by decide +kernel
-- ANCHOR_END: program

end Course.RiscQueue
