namespace PEL4

/-- Represents the 4-valued Belnap-Dunn logic (First Degree Entailment). -/
structure FDEValue where
  pos : Bool
  neg : Bool
  deriving DecidableEq, Repr

/-- The four core truth values. -/
def FDEValue.T : FDEValue := { pos := true, neg := false }
def FDEValue.B : FDEValue := { pos := true, neg := true }
def FDEValue.N : FDEValue := { pos := false, neg := false }
def FDEValue.F : FDEValue := { pos := false, neg := true }

/-- Logical negation. -/
def FDEValue.not (v : FDEValue) : FDEValue :=
  { pos := v.neg, neg := v.pos }

/-- Logical conjunction. -/
def FDEValue.and (v1 v2 : FDEValue) : FDEValue :=
  { pos := v1.pos && v2.pos, neg := v1.neg || v2.neg }

/-- Logical disjunction. -/
def FDEValue.or (v1 v2 : FDEValue) : FDEValue :=
  { pos := v1.pos || v2.pos, neg := v1.neg && v2.neg }

/-- Strict-to-Tolerant (ST) validity: If premise is strictly true (T), conclusion must be at least tolerated (T or B). -/
def ST_valid (premise conclusion : FDEValue) : Prop :=
  (premise = FDEValue.T) → (conclusion = FDEValue.T ∨ conclusion = FDEValue.B)

/-- Tolerant-to-Tolerant (LP) validity: If premise is tolerated (T or B), conclusion must be tolerated. -/
def LP_valid (premise conclusion : FDEValue) : Prop :=
  (premise = FDEValue.T ∨ premise = FDEValue.B) → (conclusion = FDEValue.T ∨ conclusion = FDEValue.B)

end PEL4
