import MiniRisc.Model

namespace Course.MiniRisc

-- ANCHOR: instructionSemantics
inductive Exec : Instruction → State → State → Prop where
  | add : Exec (.add rd rs1 rs2) state
      ({ state with pc := state.pc + 4 }.writeReg rd (state.readReg rs1 + state.readReg rs2))
  | addi : Exec (.addi rd rs1 immediate) state
      ({ state with pc := state.pc + 4 }.writeReg rd (state.readReg rs1 + signed immediate))
  | beqTaken (equal : state.readReg rs1 = state.readReg rs2)
      (aligned : (state.pc + signed offset).toNat % 4 = 0) :
      Exec (.beq rs1 rs2 offset) state { state with pc := state.pc + signed offset }
  | beqNext (different : state.readReg rs1 ≠ state.readReg rs2) :
      Exec (.beq rs1 rs2 offset) state { state with pc := state.pc + 4 }
  | bneTaken (different : state.readReg rs1 ≠ state.readReg rs2)
      (aligned : (state.pc + signed offset).toNat % 4 = 0) :
      Exec (.bne rs1 rs2 offset) state { state with pc := state.pc + signed offset }
  | bneNext (equal : state.readReg rs1 = state.readReg rs2) :
      Exec (.bne rs1 rs2 offset) state { state with pc := state.pc + 4 }
-- ANCHOR_END: instructionSemantics

-- ANCHOR: faultSemantics
inductive ExecFault : Instruction → State → Fault → Prop where
  | breakpoint : ExecFault .ebreak state .breakpoint
  | beqMisaligned (equal : state.readReg rs1 = state.readReg rs2)
      (bad : (state.pc + signed offset).toNat % 4 ≠ 0) :
      ExecFault (.beq rs1 rs2 offset) state (.misaligned (state.pc + signed offset))
  | bneMisaligned (different : state.readReg rs1 ≠ state.readReg rs2)
      (bad : (state.pc + signed offset).toNat % 4 ≠ 0) :
      ExecFault (.bne rs1 rs2 offset) state (.misaligned (state.pc + signed offset))

inductive Faulted (program : Program) : State → Fault → Prop where
  | fetch (failed : fetch program state.pc = .error fault) : Faulted program state fault
  | execute (fetched : fetch program state.pc = .ok instruction)
      (failed : ExecFault instruction state fault) : Faulted program state fault
-- ANCHOR_END: faultSemantics

-- ANCHOR: executionSteps
inductive Step (program : Program) : State → State → Prop where
  | instruction (fetched : fetch program state.pc = .ok instruction)
      (executed : Exec instruction state next) : Step program state next

inductive Steps (program : Program) : Nat → State → State → Prop where
  | refl : Steps program 0 state state
  | next (first : Step program state middle) (rest : Steps program count middle final) :
      Steps program (count + 1) state final
-- ANCHOR_END: executionSteps

end Course.MiniRisc
