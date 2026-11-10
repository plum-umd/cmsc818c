import RiscQueue.Fixtures

def main : IO UInt32 := do
  if Course.RiscQueue.Fixtures.candidateChecks then
    IO.println "Ring checks passed. Complete the proofs and run policyChecks verifiedRing."
    return 0
  else
    IO.eprintln "Queue checks failed. Implement dequeue and the persistent pop/push adapters."
    return 1
