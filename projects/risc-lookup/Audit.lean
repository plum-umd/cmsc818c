import Checks
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `Plos.RiscV.Lookup.program then
    throwError "Import only PL/OS infrastructure, not the completed upstream lookup."

#print axioms Plos.RiscV.CodeAt.step
#print axioms Plos.RiscV.resumeCall_sound
#print axioms Plos.RiscV.Returns.run
#print axioms Course.RiscLookup.code
#print axioms Course.RiscLookup.Support.step_at
#print axioms Course.RiscLookup.Support.not_return

-- After importing your solution, add #print axioms for each submitted theorem here.
