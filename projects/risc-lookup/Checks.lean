import RiscLookup.Fixtures

open Plos.RiscV Course.RiscLookup.Fixtures

private def loaded (result : Except Fault Nat) : Option Nat := result.toOption

private def fault (result : Except Fault Nat) : Option Fault :=
  match result with
  | .ok _ => none
  | .error error => some error

-- Infrastructure checks; these do not claim the empty student routine is correct.
#guard dataBytes [0, 0x0102030405060708] =
  #[0, 0, 0, 0, 0, 0, 0, 0, 8, 7, 6, 5, 4, 3, 2, 1]
#guard loaded ((initial #[] 0 [42]).memory.load .user .read 1024 .double) = some 42
#guard fault ((initial #[] 0 [42] false).memory.load .user .read 1024 .double) =
  some (.accessDenied .read 1024)
#guard fault ((initial #[] 0 [42]).memory.load .user .read 1026 .double) =
  some (.misaligned .read 1026)
#guard (resumeCall 64 0 { pc := 64 }).stop = .returned
#guard (resumeCall 64 0 {}).stop = .suspended

-- Exercise the fixture with a separate, one-instruction return harness, not a lookup solution.
private def returnCode : Array InstructionWord :=
  #[(Assembler.encode (.jalr 0 1 0)).toOption.get (by decide +kernel)]

#guard (callRoutine (invocation returnCode 0 0 0) 1
  (initial returnCode 0 [])).toOption.map (·.stop) = some .returned
#guard (callRoutine (invocation returnCode 256 0 0) 1
  (initial returnCode 256 [])).toOption.map (·.state.pc) = some 264

-- Reject vacuous implementations without depending on the student's changing program.
#guard !checkProgram #[]
#guard !checkProgram returnCode

-- Import RiscLookup.Solution here when you have written your proofs.
