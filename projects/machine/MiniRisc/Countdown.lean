import MiniRisc.Model

namespace Course.MiniRisc

-- ANCHOR: countdown
def countdown : Program := {
  code := #[
    .beq 10 0 12,
    .addi 10 10 (BitVec.ofInt 12 (-1)),
    .beq 0 0 (BitVec.ofInt 13 (-8)),
    .ebreak] }

def start (value : Word) : State := ({} : State).writeReg 10 value
-- ANCHOR_END: countdown

end Course.MiniRisc
