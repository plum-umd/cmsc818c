import TinyCompiler.Correctness

namespace Course.TinyCompiler.Examples

open Course.MiniRisc

-- ANCHOR: sourceExample
def exampleProgram : Stmt :=
  .seq (.assign 0 (.literal 7))
    (.seq (.assign 1 (.literal (BitVec.ofInt 12 (-7))))
      (.seq (.assign 0 (.add 0 1))
        (.ifzero 0 (.assign 2 (.literal 42)) (.assign 2 (.literal 99)))))
-- ANCHOR_END: sourceExample

def machineStore (store : Store) (base : Nat) : State := {
  registers := Vector.ofFn fun register =>
    if h : 1 ≤ register.val ∧ register.val ≤ 30 then store.read ⟨register.val - 1, by omega⟩
    else 0
  pc := BitVec.ofNat 64 base }

def runCompiled (base : Nat) (statement : Stmt) (store : Store) : Option RunResult := do
  let program ← (compile base statement).toOption
  return run ((emit statement).length + 1) program (machineStore store base)

end Course.TinyCompiler.Examples
