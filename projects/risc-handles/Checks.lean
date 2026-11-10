import RiscHandles.Fixtures

open Plos.RiscV Course.RiscHandles

-- Loader and representation checks, independent of the student's unfinished assembly.
example : (Native.init [7, 0] 4).Valid := Native.init_valid _ _ (by decide +kernel)
  (by decide) (by decide)
example : (Native.init [7, 0] 4).words = [7, 0] := Native.init_words _ _ (by decide +kernel)
  (by decide) (by decide)
#guard ((Native.init [7, 0] 4).lookupResult 1).state.readReg 10 = 0
#guard ((Native.init [7, 0] 4).lookupResult 1).state.readReg 11 = 1
#guard ((Native.init [7, 0] 4).lookupResult 2).state.readReg 11 = 0
#guard ((Native.init [7, 0] 4).memory.load .user .read 264 .double).toOption = some 0

-- Reject an empty implementation and a routine that merely returns.
private def returnOnly : Array InstructionWord :=
  #[(Assembler.encode (.jalr 0 1 0)).toOption.get (by decide +kernel)]
#guard !Fixtures.checkRoutine #[]
#guard !Fixtures.checkRoutine returnOnly

-- Import RiscHandles.Solution here after implementing the routine, adapter, and proofs.
