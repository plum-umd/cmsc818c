import Queue.Model

namespace Course.Queue.Buffer

-- ANCHOR: bufferState
structure State where
  slots : Array Word
  head : Nat
  count : Nat
  deriving Repr, DecidableEq

/-- Storage size is fixed by the client, rather than duplicated in runtime metadata. -/
def Valid (capacity : Nat) (buffer : State) : Prop :=
  0 < capacity ∧ buffer.slots.size = capacity ∧
    buffer.head < capacity ∧ buffer.count ≤ capacity

/-- Total observation; validity will establish that occupied reads are in bounds. -/
def contents (slots : Array Word) (head count : Nat) : List Word :=
  (List.range count).map fun i => slots[(head + i) % slots.size]?.getD 0

def view (buffer : State) : List Word := contents buffer.slots buffer.head buffer.count

def Rep (capacity : Nat) (buffer : State) (queue : List Word) : Prop :=
  Valid capacity buffer ∧ view buffer = queue
-- ANCHOR_END: bufferState

-- ANCHOR: bufferOperations
def empty (capacity : Nat) : State := ⟨Array.replicate capacity 0, 0, 0⟩

def push (buffer : State) (value : Word) : Reply × State :=
  if buffer.count < buffer.slots.size then
    (.ok, { buffer with
      slots := buffer.slots.setIfInBounds ((buffer.head + buffer.count) % buffer.slots.size) value
      count := buffer.count + 1 })
  else (.full, buffer)

def pop (buffer : State) : Reply × State :=
  if buffer.count = 0 then (.empty, buffer)
  else
    (.value (buffer.slots[buffer.head]?.getD 0),
      { buffer with head := (buffer.head + 1) % buffer.slots.size, count := buffer.count - 1 })

def run (buffer : State) : Command → Reply × State
  | .push value => push buffer value
  | .pop => pop buffer
-- ANCHOR_END: bufferOperations

/-- Reference client execution, recording every reply, including full and empty results. -/
def referenceTrace (capacity : Nat) (queue : List Word) : List Command → List Reply × List Word
  | [] => ([], queue)
  | command :: commands =>
      let (reply, next) := Course.Queue.run capacity queue command
      let (replies, final) := referenceTrace capacity next commands
      (reply :: replies, final)

-- ANCHOR: bufferTrace
def runTrace (buffer : State) : List Command → List Reply × State
  | [] => ([], buffer)
  | command :: commands =>
      let (reply, next) := run buffer command
      let (replies, final) := runTrace next commands
      (reply :: replies, final)
-- ANCHOR_END: bufferTrace

end Course.Queue.Buffer
