import RiscHandles.Fixtures

def main : IO UInt32 := do
  if Course.RiscHandles.Fixtures.candidateChecks then
    IO.println "Handles checks passed. The universal correctness proofs are still required."
    return 0
  else
    IO.eprintln "Handles checks failed. Implement the append routine and persistent adapter."
    return 1
