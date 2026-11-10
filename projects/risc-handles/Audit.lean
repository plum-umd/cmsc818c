import Checks
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  if env.contains `Plos.RiscV.Append.program || env.contains `Plos.RiscV.NativeTable then
    throwError "Use the supplied lookup and memory infrastructure, not completed native handles."

#print axioms Plos.RiscV.Memory.store64_effect
#print axioms Plos.RiscV.Store64Effect.load_preserved
#print axioms Plos.RiscV.CodeAt.store64
#print axioms Course.RiscHandles.Image.append_code
#print axioms Course.RiscHandles.Native.init_valid
#print axioms Course.RiscHandles.Native.table
#print axioms Course.RiscHandles.code

-- Add #print axioms for your submitted theorems; Checks imports your solution.
