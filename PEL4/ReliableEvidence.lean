import PEL4.Evidence

namespace PEL4

/-!
A small reliability layer for future 6-valued extensions.

`raw` records the ordinary four-valued evidence state.  The reliability bits
record whether the positive and negative evidence channels are themselves
trusted.  This keeps the current 4-PEL algebra intact while making the
classicality/reliability operator from LET-style systems executable.
-/

structure EvidenceStatus where
  raw : FDEValue
  reliablePos : Bool
  reliableNeg : Bool
deriving DecidableEq, Repr

def reliablePositive (e : EvidenceStatus) : Bool :=
  e.raw.pos && e.reliablePos

def reliableNegative (e : EvidenceStatus) : Bool :=
  e.raw.neg && e.reliableNeg

def reliabilityProjection (e : EvidenceStatus) : FDEValue :=
  { pos := reliablePositive e, neg := reliableNegative e }

def hasReliableGlut (e : EvidenceStatus) : Bool :=
  isGlut (reliabilityProjection e)

def hasUnreliableGlut (e : EvidenceStatus) : Bool :=
  isGlut e.raw && !hasReliableGlut e

def classicallyReliable (e : EvidenceStatus) : Bool :=
  isClassical (reliabilityProjection e)

def rawGlutReliableOnOneSide : EvidenceStatus :=
  { raw := FDEValue.B, reliablePos := true, reliableNeg := false }

def rawGlutReliableOnBothSides : EvidenceStatus :=
  { raw := FDEValue.B, reliablePos := true, reliableNeg := true }

#eval! reliabilityProjection rawGlutReliableOnOneSide
#eval! hasReliableGlut rawGlutReliableOnOneSide
#eval! hasReliableGlut rawGlutReliableOnBothSides

end PEL4
