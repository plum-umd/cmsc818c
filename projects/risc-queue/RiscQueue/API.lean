import RiscQueue.Writer

namespace Course.RiscQueue

open Plos.RiscV

-- ANCHOR: popCorrect
structure PopCorrect (ring : Ring) : Prop where
  returned : ring.popResult.stop = .returned
  found : ring.popResult.state.readReg 13 = 1
  value : ring.pop.1 = ring.popResult.state.readReg 10
  valid : ring.pop.2.Valid
  memory : ring.pop.2.memory = ring.memory
  capacity : ring.pop.2.capacity = ring.capacity
  head : ring.pop.2.head = (ring.popResult.state.readReg 11).toNat
  count : ring.pop.2.count = (ring.popResult.state.readReg 12).toNat
  words : ring.pop.1 :: ring.pop.2.words = ring.words
-- ANCHOR_END: popCorrect

-- ANCHOR: pushCorrect
structure PushCorrect (ring : Ring) (value : Word) : Prop where
  returned :
    (ring.writeResult (View.slot ring.head ring.capacity ring.count) value).stop = .returned
  valid : (ring.push value).Valid
  memory : (ring.push value).memory =
    (ring.writeResult (View.slot ring.head ring.capacity ring.count) value).state.memory
  capacity : (ring.push value).capacity = ring.capacity
  head : (ring.push value).head = ring.head
  count : (ring.push value).count = ring.count + 1
  cells : (ring.push value).cells =
    ring.cells.set (View.slot ring.head ring.capacity ring.count) value
  words : (ring.push value).words = ring.words ++ [value]
-- ANCHOR_END: pushCorrect

-- ANCHOR: correctRing
/-- A proof bundle to construct from student theorems, never an assumed axiom. -/
structure CorrectRing : Prop where
  pop : ∀ ring : Ring, ring.Valid → 0 < ring.count → PopCorrect ring
  push : ∀ (ring : Ring) (value : Word), ring.Valid → ring.count < ring.capacity →
    PushCorrect ring value
-- ANCHOR_END: correctRing

end Course.RiscQueue
