import RiscLookup.Fixtures

def main : IO UInt32 := do
  if Course.RiscLookup.Fixtures.candidateChecks then
    IO.println "Lookup checks passed. The universal correctness proofs are still required."
    return 0
  else
    IO.eprintln "Lookup checks failed. Implement RiscLookup/Program.lean before running this check."
    return 1
