import RiscQueue.Calls

namespace Course.RiscQueue.Ring

open Plos.RiscV

def popPrepared (ring : Ring) : State :=
  (ring.popCall.prepare { memory := ring.memory }).toOption.get (by
    simp [popCall, Call.prepare]; rfl)

-- ANCHOR: nativeCalls
def popResult (ring : Ring) : CallResult := resumeCall 192 16 ring.popPrepared

def writePrepared (ring : Ring) (index : Nat) (value : Word) : State :=
  ((ring.writeCall index value).prepare { memory := ring.memory }).toOption.get (by
    simp [writeCall, Append.invocation, Call.prepare]; rfl)

/-- Bounded append writes one physical cell, with the physical index passed as its length. -/
def writeResult (ring : Ring) (index : Nat) (value : Word) : CallResult :=
  resumeCall 192 Append.allowance (ring.writePrepared index value)
-- ANCHOR_END: nativeCalls

-- ANCHOR: adapters
/-- Implement using the encoded dequeue result's value, head, and count. -/
def pop (ring : Ring) : Word × Ring := (0, ring)

/-- Implement using the verified write at the unused tail slot; retain its resulting memory. -/
def push (ring : Ring) (_value : Word) : Ring := ring
-- ANCHOR_END: adapters

end Course.RiscQueue.Ring
