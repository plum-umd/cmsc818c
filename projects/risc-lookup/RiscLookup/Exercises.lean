import RiscLookup.Spec
import RiscLookup.Program

namespace Course.RiscLookup.Exercises

open Plos.RiscV

-- ANCHOR: runCorrect
/-- Prove this proposition for your assembled routine, at every permitted location and input. -/
def RunCorrect : Prop :=
  ∀ (state : State) (base ret : Word) (channels : List Word) (index fuel : Nat),
    Inputs code state base ret channels index → 16 ≤ fuel →
      Correct channels index ret state (resumeCall ret fuel state)
-- ANCHOR_END: runCorrect

-- ANCHOR: callCorrect
/-- Transfer the result to the public call interface; the frame starts after preparation. -/
def CallCorrect : Prop :=
  ∀ (call : Call) (original prepared : State) (channels : List Word) (index fuel : Nat),
    call.prepare original = .ok prepared →
    Inputs code prepared call.entry call.returnAddress channels index → 16 ≤ fuel →
      ∃ result, callRoutine call fuel original = .ok result ∧
        Correct channels index call.returnAddress prepared result
-- ANCHOR_END: callCorrect

end Course.RiscLookup.Exercises
