import TinyCompiler.Examples

open Course.MiniRisc Course.TinyCompiler Course.TinyCompiler.Examples

private def error? (result : Except CompileError α) : Option CompileError :=
  match result with
  | .ok _ => none
  | .error error => some error

#guard (eval exampleProgram {}).read 0 = 0
#guard (eval exampleProgram {}).read 2 = 42
#guard ((runCompiled 0 exampleProgram {}).map (·.state.readReg (reg 2))) = some 42
#guard ((runCompiled 0 exampleProgram {}).map (·.stop)) = some (.trapped .breakpoint)
#guard ((runCompiled 4096 exampleProgram {}).map (·.state.readReg (reg 2))) = some 42

-- Both conditional paths, including empty arms, must reach the exit marker.
#guard ((runCompiled 0 (.ifzero 0 .skip .skip) {}).map (·.retired)) = some 2
#guard ((runCompiled 0 (.ifzero 0 .skip .skip) (({} : Store).write 0 1)).map (·.retired)) = some 1
#guard ((runCompiled 0 .skip {}).map (·.retired)) = some 0
#guard ((runCompiled 0 .skip {}).map (·.stop)) = some (.trapped .breakpoint)
#guard ((runCompiled 0 (.ifzero 0 (.assign 1 (.literal 7)) (.assign 1 (.literal 9)))
  (({} : Store).write 0 1)).map (·.state.readReg (reg 1))) = some 9
#guard ((runCompiled 0
  (.ifzero 0 (.ifzero 1 (.assign 2 (.literal 7)) (.assign 2 (.literal 8)))
    (.assign 2 (.literal 9)))
  (({} : Store).write 1 1)).map (·.state.readReg (reg 2))) = some 8

-- Unwritten registers, including the reserved register, survive the compiled code.
#guard
  let statement := Stmt.assign 0 (.literal 1)
  let program := (compile 0 statement).toOption.getD ⟨0, #[]⟩
  let initial := (({} : State).writeReg 31 123).writeReg (reg 1) 55
  let result := run 2 program initial
  (result.state.readReg 31, result.state.readReg (reg 1)) = (123, 55)

-- Aliasing and arithmetic wrap use the pre-state and modular source semantics.
private def doubleSelf : Stmt := .assign 0 (.add 0 0)
private def maxInput : Store := ({} : Store).write 0 (BitVec.ofNat 64 (2^64 - 1))
#guard (eval doubleSelf maxInput).read 0 = BitVec.ofNat 64 (2^64 - 2)
#guard ((runCompiled 0 doubleSelf maxInput).map (·.state.readReg (reg 0))) =
  some (BitVec.ofNat 64 (2^64 - 2))
#guard error? (compile 2 .skip) = some .misalignedBase
#guard error? (compile (2^64) .skip) = some .addressOverflow
#guard ((runCompiled (2^64 - 4) .skip {}).map (·.stop)) = some (.trapped .breakpoint)

-- Oversized code is rejected, even though raw emission would truncate branch fields.
private def copies : Nat → Stmt
  | 0 => .skip
  | n + 1 => .seq (.assign 0 (.var 0)) (copies n)

-- The maximum forward branch is accepted without changing its signed displacement.
set_option maxRecDepth 4096 in
#guard ((compile 0 (.ifzero 0 (copies 1021) .skip)).toOption.map (·.code.size)) = some 1024

set_option maxRecDepth 4096 in
#guard ((runCompiled 0 (.ifzero 0 (copies 1021) .skip) (({} : Store).write 0 1)).map
  fun result => (result.stop, result.retired)) = some (.trapped .breakpoint, 1)

set_option maxRecDepth 4096 in
#guard error? (compile 0 (.ifzero 0 (copies 1023) .skip)) = some .codeTooLarge
