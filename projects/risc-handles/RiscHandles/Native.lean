import RiscHandles.Calls

namespace Course.RiscHandles

open Plos.RiscV

namespace Native

-- ANCHOR: calls
def appendPrepared (table : Native) (channel : Word) : State :=
  ((table.appendCall channel).prepare { memory := table.memory }).toOption.get (by
    simp [appendCall, Call.prepare]; rfl)

def appendResult (table : Native) (channel : Word) : CallResult :=
  resumeCall 192 16 (table.appendPrepared channel)

def lookupPrepared (table : Native) (index : Nat) : State :=
  ((table.lookupCall index).prepare { memory := table.memory }).toOption.get (by
    simp [lookupCall, Lookup.invocation, Call.prepare]; rfl)

def lookupResult (table : Native) (index : Nat) : CallResult :=
  resumeCall 44 Lookup.allowance (table.lookupPrepared index)
-- ANCHOR_END: calls

-- ANCHOR: append
/-- Replace this placeholder with an adapter that retains the native call's memory and length. -/
def append (table : Native) (_channel : Word) : Native := table
-- ANCHOR_END: append

end Native
end Course.RiscHandles
