import PEL4.Evidence

namespace PEL4

/-!
A minimal entrenchment-based revision prototype.

This is not a full belief-revision calculus.  It is an executable core for the
idea that contradictory evidence can be revised by comparing the entrenchment
of the positive and negative channels.
-/

structure EntrenchedEvidence where
  value : FDEValue
  posRank : Nat
  negRank : Nat
deriving DecidableEq, Repr

def reviseByEntrenchment (e : EntrenchedEvidence) : FDEValue :=
  if isGlut e.value then
    if e.posRank > e.negRank then FDEValue.T
    else if e.negRank > e.posRank then FDEValue.F
    else FDEValue.B
  else e.value

def keepBothWhenEquallyEntrenched : EntrenchedEvidence :=
  { value := FDEValue.B, posRank := 2, negRank := 2 }

def keepPositiveWhenMoreEntrenched : EntrenchedEvidence :=
  { value := FDEValue.B, posRank := 3, negRank := 1 }

def keepNegativeWhenMoreEntrenched : EntrenchedEvidence :=
  { value := FDEValue.B, posRank := 1, negRank := 3 }

#eval! reviseByEntrenchment keepBothWhenEquallyEntrenched
#eval! reviseByEntrenchment keepPositiveWhenMoreEntrenched
#eval! reviseByEntrenchment keepNegativeWhenMoreEntrenched

end PEL4
