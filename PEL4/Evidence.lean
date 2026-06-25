import PEL4.FDE

namespace PEL4

/-!
Evidence-level views on Belnap-Dunn values.

The core `FDEValue` type already stores two independent bits.  This module
names the intended 4-PEL reading of those bits: positive evidence and negative
evidence can be present independently, jointly, or not at all.
-/

def FDEValue.ofBool (b : Bool) : FDEValue :=
  if b then FDEValue.T else FDEValue.F

def hasPositiveEvidence (v : FDEValue) : Bool :=
  v.pos

def hasNegativeEvidence (v : FDEValue) : Bool :=
  v.neg

def isGlut (v : FDEValue) : Bool :=
  v.pos && v.neg

def isGap (v : FDEValue) : Bool :=
  !v.pos && !v.neg

def isDetermined (v : FDEValue) : Bool :=
  v.pos || v.neg

def isContradictory (v : FDEValue) : Bool :=
  isGlut v

def isConsistent (v : FDEValue) : Bool :=
  !isContradictory v

def isClassical (v : FDEValue) : Bool :=
  decide (v = FDEValue.T) || decide (v = FDEValue.F)

#eval! hasPositiveEvidence FDEValue.B
#eval! hasNegativeEvidence FDEValue.B
#eval! isGlut FDEValue.B
#eval! isGap FDEValue.N
#eval! isClassical FDEValue.T

end PEL4
