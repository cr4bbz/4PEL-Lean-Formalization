import PEL4.UnknownUnknowns

namespace PEL4

/-!
# Gate 102: contradictory model evidence

Gate 101 represented model-class doubt as the 4PEL gap `N`. Gate 102 separates
that state from a genuine meta-level glut. Two independent diagnostic channels
can strongly support and strongly defeat the proposition that the known model
class is adequate, producing `B` rather than `N`.
-/

structure Gate102MetaEvidence where
  adequacySupport : Rat
  inadequacySupport : Rat
  deriving DecidableEq, Repr

/-- Weak evidence on both sides: a meta-epistemic gap. -/
def gate102GapEvidence : Gate102MetaEvidence :=
  { adequacySupport := (1 : Rat) / 2
    inadequacySupport := (1 : Rat) / 2 }

/-- Independent diagnostics strongly pull in opposite directions. -/
def gate102ConflictEvidence : Gate102MetaEvidence :=
  { adequacySupport := (4 : Rat) / 5
    inadequacySupport := (4 : Rat) / 5 }

/-- A clean validation result. -/
def gate102ValidatedEvidence : Gate102MetaEvidence :=
  { adequacySupport := (9 : Rat) / 10
    inadequacySupport := (1 : Rat) / 10 }

/-- A clean refutation result. -/
def gate102RefutedEvidence : Gate102MetaEvidence :=
  { adequacySupport := (1 : Rat) / 10
    inadequacySupport := (9 : Rat) / 10 }

def gate102AsEvidenceState (e : Gate102MetaEvidence) : Gate77EvidenceState :=
  { posSupport := e.adequacySupport
    negSupport := e.inadequacySupport }

def gate102Status (e : Gate102MetaEvidence) : FDEValue :=
  gate77Status (gate102AsEvidenceState e)

theorem gate102_gap_is_N :
    gate102Status gate102GapEvidence = FDEValue.N := by
  native_decide

theorem gate102_conflict_is_B :
    gate102Status gate102ConflictEvidence = FDEValue.B := by
  native_decide

theorem gate102_validation_is_T :
    gate102Status gate102ValidatedEvidence = FDEValue.T := by
  native_decide

theorem gate102_refutation_is_F :
    gate102Status gate102RefutedEvidence = FDEValue.F := by
  native_decide

/-- Gate 101's anomaly-induced gap and Gate 102's conflict are extensionally
separate four-valued meta-states. -/
theorem gate102_unknownness_is_not_contradiction :
    gate101AdequacyStatus (gate101BeliefAfter .anomaly) = FDEValue.N ∧
    gate102Status gate102ConflictEvidence = FDEValue.B ∧
    FDEValue.N ≠ FDEValue.B := by
  native_decide

/-- Main Gate-102 theorem: strong independent support for adequacy and inadequacy
produces a genuine contradiction at the level of the epistemic model itself,
without collapsing it into mere missing information. -/
theorem gate102_meta_contradiction_is_genuine_glut :
    gate102ConflictEvidence.adequacySupport ≥ (3 : Rat) / 4 ∧
    gate102ConflictEvidence.inadequacySupport ≥ (3 : Rat) / 4 ∧
    gate102Status gate102ConflictEvidence = FDEValue.B := by
  native_decide

/-!
## Boundary

The two support channels are explicit finite witnesses; Gate 102 does not derive
them from a generic diagnostic network. The verified result is structural: at
second order, lack of model knowledge (`N`) and contradictory model evidence (`B`)
remain formally distinct.
-/

end PEL4
