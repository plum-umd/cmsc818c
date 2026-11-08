import MiniRisc

open Course.MiniRisc

private def fault? (result : Except Fault α) : Option Fault :=
  match result with
  | .ok _ => none
  | .error fault => some fault

#guard (execute (start 7) (.addi 10 10 (BitVec.ofInt 12 (-1)))).toOption =
  some ((start 6) |> fun state => { state with pc := 4 })
#guard (execute (start (BitVec.ofNat 64 (2^64 - 1))) (.addi 10 10 1)).toOption =
  some { (start 0) with pc := 4 }
#guard (execute (start 7) (.add 0 10 10)).toOption = some { (start 7) with pc := 4 }

-- Alignment is checked for a taken branch, not an unused target.
#guard fault? (execute (start 0) (.beq 10 0 2)) = some (.misaligned 2)
#guard (execute (start 7) (.beq 10 0 2)).toOption = some { (start 7) with pc := 4 }
#guard fault? (execute (start 7) (.bne 10 0 2)) = some (.misaligned 2)
#guard (execute (start 0) (.bne 10 0 2)).toOption = some { (start 0) with pc := 4 }
#guard fault? (fetch countdown 2) = some (.misaligned 2)
#guard fault? (fetch countdown 16) = some (.outsideCode 16)

-- Zero fuel does not fetch, even from an invalid PC.
#guard run 0 countdown { (start 7) with pc := 2 } =
  ⟨{ (start 7) with pc := 2 }, .suspended, 0⟩
#guard run 1 countdown { (start 7) with pc := 2 } =
  ⟨{ (start 7) with pc := 2 }, .trapped (.misaligned 2), 0⟩

#guard (run 1 countdown (start 0)).stop = .suspended
#guard (run 1 countdown (start 0)).state.pc = 12
#guard (run 2 countdown (start 0)).stop = .trapped .breakpoint
#guard (run 2 countdown (start 0)).retired = 1
#guard (run 10 countdown (start 3)).stop = .suspended
#guard (run 10 countdown (start 3)).state.readReg 10 = 0
#guard (run 11 countdown (start 3)).stop = .trapped .breakpoint
#guard (run 11 countdown (start 3)).retired = 10

-- Suspension resumes from the saved PC and register file.
#guard
  let first := run 4 countdown (start 3)
  let second := run 7 countdown first.state
  run 11 countdown (start 3) = { second with retired := first.retired + second.retired }

-- A final instruction can retire at the last aligned address; fall-through wraps.
#guard (fetch ⟨2^64 - 4, #[.addi 10 0 1]⟩ (BitVec.ofNat 64 (2^64 - 4))).toOption =
  some (.addi 10 0 1)
#guard (execute { (start 7) with pc := BitVec.ofNat 64 (2^64 - 4) } (.addi 10 0 1)).toOption =
  some (start 1)
