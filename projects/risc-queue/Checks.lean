import RiscQueue.Fixtures

open Plos.RiscV Course.RiscQueue

-- Supplied loader and writer checks, independent of unfinished dequeue and adapters.
example : (Ring.init [7, 0] 4).Valid := Ring.init_valid _ _ (by decide) (by decide) (by decide)
example : (Ring.init [7, 0] 4).words = [7, 0] := Ring.init_words _ _ (by decide) (by decide)
#guard (Ring.init [7, 0] 4).cells = [7, 0, 0, 0]
#guard (Ring.init [7, 0] 4).view = [7, 0]
#guard ((Ring.init [7] 4).writeResult 3 42).stop = .returned
#guard (((Ring.init [7] 4).writeResult 3 42).state.memory.load .user .read 280 .double).toOption =
  some 42
#guard View.slot 3 4 0 = 3
#guard View.slot 3 4 1 = 0
#guard View.slot 3 4 2 = 1
#guard Policy.view (Policy.fromList [1, 1, 2]) = [1, 1, 2]
#guard Policy.view (Policy.remove (Policy.fromList [1, 1, 2]) 1) = [2]
#guard Policy.view (Policy.fromList [2^64+3]) = [2^64+3]

private def returnOnly : Array InstructionWord :=
  #[(Assembler.encode (.jalr 0 1 0)).toOption.get (by decide +kernel)]
#guard !Fixtures.checkRoutine #[]
#guard !Fixtures.checkRoutine returnOnly

-- Import RiscQueue.Solution here.
-- In that solution, run #guard Fixtures.policyChecks verifiedRing.
