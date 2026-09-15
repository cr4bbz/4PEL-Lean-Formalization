import PEL4.PosteriorSurprise
import PEL4.EpistemicSelfDoubtBridge

namespace PEL4

/-!
# Gate 101: unknown unknowns and the epistemic gap

Gate 99 can detect predictive failure of the known model class. Gate 101 refuses
to force all probability mass back into that class. Model doubt opens explicit
mass for an outside-class possibility, and the adequacy proposition for the known
class is evaluated with the existing Gate-77 four-valued evidence semantics.
-/

structure Gate101OpenModelBelief where
  lowMass : Rat
  highMass : Rat
  unknownMass : Rat
  deriving DecidableEq, Repr

/-- Closed-class state before model doubt. -/
def gate101ClosedBelief : Gate101OpenModelBelief :=
  { lowMass := (1 : Rat) / 2
    highMass := (1 : Rat) / 2
    unknownMass := 0 }

/-- Model doubt reserves half the mass for an omitted model. -/
def gate101DoubtBelief : Gate101OpenModelBelief :=
  { lowMass := (1 : Rat) / 4
    highMass := (1 : Rat) / 4
    unknownMass := (1 : Rat) / 2 }

def gate101KnownMass (belief : Gate101OpenModelBelief) : Rat :=
  belief.lowMass + belief.highMass

def gate101TotalMass (belief : Gate101OpenModelBelief) : Rat :=
  gate101KnownMass belief + belief.unknownMass

/-- Gate-99 meta-mode determines whether outside-class mass is opened. -/
def gate101BeliefAfter (obs : Gate99Observation) : Gate101OpenModelBelief :=
  match gate99MetaUpdate obs with
  | .normalUpdate => gate101ClosedBelief
  | .modelDoubt => gate101DoubtBelief

/-- Evidence for the proposition "the currently known model class is adequate".
Known mass supports adequacy; unknown mass independently supports its negation. -/
def gate101AdequacyEvidence (belief : Gate101OpenModelBelief) : Gate77EvidenceState :=
  { posSupport := gate101KnownMass belief
    negSupport := belief.unknownMass }

def gate101AdequacyStatus (belief : Gate101OpenModelBelief) : FDEValue :=
  gate77Status (gate101AdequacyEvidence belief)

theorem gate101_beliefs_normalized :
    gate101TotalMass gate101ClosedBelief = 1 ∧
    gate101TotalMass gate101DoubtBelief = 1 := by
  native_decide

theorem gate101_closed_class_is_strictly_supported :
    gate101AdequacyStatus gate101ClosedBelief = FDEValue.T := by
  native_decide

theorem gate101_model_doubt_opens_unknown_mass :
    (gate101BeliefAfter .anomaly).unknownMass = (1 : Rat) / 2 := by
  native_decide

theorem gate101_routine_keeps_unknown_mass_zero :
    (gate101BeliefAfter .routine).unknownMass = 0 := by
  native_decide

theorem gate101_anomaly_creates_adequacy_gap :
    gate101AdequacyStatus (gate101BeliefAfter .anomaly) = FDEValue.N := by
  native_decide

/-- Main Gate-101 theorem: sufficient predictive surprise moves a proposition
about model-class adequacy from strict support `T` to the 4PEL gap `N`, while the
probability state remains normalized by assigning mass outside the known class. -/
theorem gate101_unknown_unknowns_bridge :
    gate101AdequacyStatus gate101ClosedBelief = FDEValue.T ∧
    gate99MetaUpdate .anomaly = .modelDoubt ∧
    (gate101BeliefAfter .anomaly).unknownMass = (1 : Rat) / 2 ∧
    gate101TotalMass (gate101BeliefAfter .anomaly) = 1 ∧
    gate101AdequacyStatus (gate101BeliefAfter .anomaly) = FDEValue.N := by
  native_decide

/-!
## Boundary

The amount of outside-class mass is a finite design witness rather than a generic
Bayesian nonparametric update. The verified structural point is that explicit
unknown-model mass can preserve normalization without pretending that a known
model is adequate, and that this state maps naturally to existing 4PEL `N`.
-/

end PEL4
