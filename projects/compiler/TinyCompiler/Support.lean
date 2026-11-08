import MiniRisc.Model

namespace Course.TinyCompiler.Support

open Course.MiniRisc

@[simp] theorem read_write_self (state : State) (rd : Register) (value : Word)
    (nonzero : rd.val ≠ 0) : (state.writeReg rd value).readReg rd = value := by
  simp [State.writeReg, State.readReg, nonzero]

theorem read_write_other (state : State) (rd other : Register) (value : Word)
    (different : other ≠ rd) : (state.writeReg rd value).readReg other = state.readReg other := by
  have indices : rd.val ≠ other.val := fun same => different (Fin.ext same.symm)
  by_cases zero : rd.val = 0 <;> simp [State.writeReg, State.readReg, zero, indices]

-- ANCHOR: runComposition
theorem run_append (firstFuel secondFuel : Nat) (program : Program) (state : State)
    (suspended : (run firstFuel program state).stop = .suspended) :
    run (firstFuel + secondFuel) program state =
      let first := run firstFuel program state
      let second := run secondFuel program first.state
      { second with retired := first.retired + second.retired } := by
  induction firstFuel generalizing state with
  | zero => simp [run]
  | succ fuel ih =>
      cases stepped : step program state with
      | error fault => simp [run, stepped] at suspended
      | ok next =>
          have nextSuspended : (run fuel program next).stop = .suspended := by
            simpa [run, stepped] using suspended
          have rest := ih next nextSuspended
          simp only [Nat.succ_add, run, stepped]
          rw [rest]
-- ANCHOR_END: runComposition

end Course.TinyCompiler.Support
