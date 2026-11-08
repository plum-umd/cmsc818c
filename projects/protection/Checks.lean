import ProtectedMemory
import ProtectedMemory.Examples

open Course.ProtectedMemory Course.ProtectedMemory.Examples

#guard (operate initial .left (.store 0x1000 0x0807060504030201)).1 = .stored
#guard (operate initial .right (.store 0x1000 7)) = (.fault .accessDenied, initial)
#guard (operate initial .left (.load 0x1010)) = (.fault .accessDenied, initial)
#guard (operate initial .left (.store 0x1001 7)) = (.fault .misaligned, initial)

private def filled : Memory := (operate initial .left (.store 0x1000 0x0807060504030201)).2
#guard filled.bytes[0]? = some 1
#guard filled.bytes[7]? = some 8
#guard operate filled .left (.load 0x1000) = (.loaded 0x0807060504030201, filled)
#guard filled.bytes[16]? = initial.bytes[16]?

-- A permitted start is insufficient: all eight bytes must belong to one authorized region.
private def shortRegion : Memory := { initial with regions := [⟨0x1000, 12, .left, true, true⟩] }
#guard operate shortRegion .left (.store 0x1008 7) = (.fault .accessDenied, shortRegion)
private def splitRegions : Memory := { initial with regions := [
  ⟨0x1000, 4, .left, true, true⟩, ⟨0x1004, 4, .left, true, true⟩] }
#guard operate splitRegions .left (.load 0x1000) = (.fault .accessDenied, splitRegions)

-- Permissions and backing bounds are checked independently, even on invalid configurations.
private def unbacked : Memory := { initial with regions := [⟨0x2000, 8, .left, true, true⟩] }
#guard operate unbacked .left (.store 0x2000 7) = (.fault .outOfBounds, unbacked)
private def readOnly : Memory := { initial with regions := [⟨0x1000, 32, .left, true, false⟩] }
#guard operate readOnly .left (.store 0x1000 7) = (.fault .accessDenied, readOnly)
#guard operate readOnly .left (.load 0x1000) = (.loaded 0, readOnly)

-- Same-owner overlap grants access if any one whole-access region permits it.
private def grants : Memory := { initial with regions := [
  ⟨0x1000, 16, .left, true, false⟩, ⟨0x1000, 16, .left, false, true⟩] }
#guard (operate grants .left (.store 0x1000 7)).1 = .stored

-- Local permission checks alone cannot establish isolation for an overlapping host policy.
private def overlap : Memory := { initial with regions := [
  ⟨0x1000, 16, .left, true, true⟩, ⟨0x1000, 16, .right, true, true⟩] }
#guard (operate overlap .left (.store 0x1000 7)).1 = .stored
#guard byteAt (operate overlap .left (.store 0x1000 7)).2 0x1000 = some 7

-- Zero is an ordinary stored value, and a denied store leaves *all* bytes unchanged.
#guard operate filled .right (.store 0x1000 0) = (.fault .accessDenied, filled)
#guard (operate filled .left (.store 0x1000 0)).1 = .stored

-- The last aligned access ends at 2^64 without wrapping the interval check.
private def top : Memory := {
  base := 2^64 - 8
  bytes := Array.replicate 8 0
  regions := [⟨2^64 - 8, 8, .left, true, true⟩] }
#guard (operate top .left (.store (BitVec.ofNat 64 (2^64 - 8)) 42)).1 = .stored
#guard operate top .left (.store (BitVec.ofNat 64 (2^64 - 4)) 42) = (.fault .misaligned, top)

#guard
  let commands := [Command.store 0x1000 7, .store 0x1010 99, .load 0x1000, .load 0x1010]
  let result := runTrace initial .left commands
  result.1 = [.stored, .fault .accessDenied, .loaded 7, .fault .accessDenied] ∧
    result.2.bytes[16]? = initial.bytes[16]?
