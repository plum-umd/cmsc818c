import Checks
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `Plos.RiscV.RingPop.program || env.contains `Plos.RiscV.NativeRing ||
      env.contains `Plos.Kernel.NativeQueue.fromList then
    throwError "Use supplied append and kernel contracts, not the completed native queue."

#print axioms Course.RiscQueue.code_bound
#print axioms Course.RiscQueue.Image.pop_code
#print axioms Course.RiscQueue.Ring.init_valid
#print axioms Course.RiscQueue.Ring.write_effect
#print axioms Plos.RiscV.Lookup.Table.set
#print axioms Course.RiscQueue.View.slot_injective

-- Add assumption reports for all submitted theorems, including the constructed CorrectRing bundle.
