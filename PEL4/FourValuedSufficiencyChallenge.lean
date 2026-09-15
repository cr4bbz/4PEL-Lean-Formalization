import PEL4.CostSensitiveSelfTrust
import PEL4.ActiveContradictionResolution

namespace PEL4

/-!
# Gate 107: four-valued sufficiency challenge

Gate 106 showed that a four-valued model status does not determine a rational
action once epistemic-action costs vary. Gate 107 asks a more severe question:
even with costs fixed, does the complete nested four-valued pair
`(worldStatus, modelStatus)` preserve enough information for optimal control?

The witness below deliberately compares two normalized quantitative beliefs that
collapse to the same nested status `T/T`. A risky action pays according to the
positive probability mass, while a safe action pays a fixed `4/5`. The two beliefs
therefore induce different optimal actions despite having exactly the same 4PEL
projection.
-/

/-- A minimal quantitative first-order belief underlying a 4PEL projection. -/
structure Gate107QuantitativeBelief where
  positiveMass : Rat
  negativeMass : Rat
  deriving DecidableEq, Repr

/-- Read the quantitative masses through Gate 77's independent `3/4` thresholds. -/
def gate107WorldEvidence (belief : Gate107QuantitativeBelief) : Gate77EvidenceState :=
  { posSupport := belief.positiveMass
    negSupport := belief.negativeMass }

/-- Gate 107 fixes second-order model trust at strict `T` and varies only the
quantitative first-order belief hidden beneath the qualitative world verdict. -/
def gate107NestedStatus (belief : Gate107QuantitativeBelief) : Gate103NestedStatus :=
  { world := gate77Status (gate107WorldEvidence belief)
    model := FDEValue.T }

/-- A strongly positive normalized belief. -/
def gate107HighBelief : Gate107QuantitativeBelief :=
  { positiveMass := (99 : Rat) / 100
    negativeMass := (1 : Rat) / 100 }

/-- A normalized belief exactly on the positive `T` threshold. -/
def gate107ThresholdBelief : Gate107QuantitativeBelief :=
  { positiveMass := (3 : Rat) / 4
    negativeMass := (1 : Rat) / 4 }

/-- Both concrete beliefs are ordinary normalized binary probability states. -/
theorem gate107_beliefs_are_normalized :
    gate107HighBelief.positiveMass + gate107HighBelief.negativeMass = 1 ∧
    gate107ThresholdBelief.positiveMass + gate107ThresholdBelief.negativeMass = 1 := by
  native_decide

/-- The coarse 4PEL projection deliberately forgets how far above threshold a
positive belief lies. Both quantitative states therefore become `T/T`. -/
theorem gate107_same_nested_four_valued_status :
    gate107NestedStatus gate107HighBelief = gate103TrustedTruth ∧
    gate107NestedStatus gate107ThresholdBelief = gate103TrustedTruth ∧
    gate107NestedStatus gate107HighBelief =
      gate107NestedStatus gate107ThresholdBelief := by
  native_decide

inductive Gate107Action where
  | safe
  | risky
  deriving DecidableEq, Repr

/-- The safe act has fixed utility `4/5`. -/
def gate107SafeValue : Rat := (4 : Rat) / 5

/-- The risky act pays one unit exactly when the positive proposition is true, so
its expected value is the positive probability mass. -/
def gate107RiskyValue (belief : Gate107QuantitativeBelief) : Rat :=
  belief.positiveMass

/-- Ties go to the safe action. -/
def gate107ChooseAction (belief : Gate107QuantitativeBelief) : Gate107Action :=
  if gate107RiskyValue belief > gate107SafeValue then .risky else .safe

/-- The high-confidence belief rationally chooses the risky act. -/
theorem gate107_high_belief_chooses_risky :
    gate107ChooseAction gate107HighBelief = .risky := by
  native_decide

/-- The threshold belief has the very same `T/T` abstraction but rationally
chooses the safe act. -/
theorem gate107_threshold_belief_chooses_safe :
    gate107ChooseAction gate107ThresholdBelief = .safe := by
  native_decide

/-- Decision sufficiency of the coarse nested status would require any two
quantitative states with the same abstraction to induce the same optimal action. -/
def gate107FourValuedControlSufficient : Prop :=
  ∀ x y : Gate107QuantitativeBelief,
    gate107NestedStatus x = gate107NestedStatus y →
      gate107ChooseAction x = gate107ChooseAction y

/-- The nested 4PEL pair is not, in general, a sufficient statistic for this
control problem. The proof is a concrete collision in the abstraction map. -/
theorem gate107_four_valued_projection_not_control_sufficient :
    ¬ gate107FourValuedControlSufficient := by
  intro hSufficient
  have hSame :
      gate107NestedStatus gate107HighBelief =
        gate107NestedStatus gate107ThresholdBelief := by
    native_decide
  have hActions := hSufficient gate107HighBelief gate107ThresholdBelief hSame
  have hDifferent :
      gate107ChooseAction gate107HighBelief ≠
        gate107ChooseAction gate107ThresholdBelief := by
    native_decide
  exact hDifferent hActions

/-- Main Gate-107 result: two normalized quantitative beliefs can collapse to the
same nested `T/T` status while demanding different value-optimal actions. -/
theorem gate107_four_valued_sufficiency_challenge :
    gate107NestedStatus gate107HighBelief = gate103TrustedTruth ∧
    gate107NestedStatus gate107ThresholdBelief = gate103TrustedTruth ∧
    gate107ChooseAction gate107HighBelief = .risky ∧
    gate107ChooseAction gate107ThresholdBelief = .safe ∧
    ¬ gate107FourValuedControlSufficient := by
  exact ⟨gate107_same_nested_four_valued_status.1,
    gate107_same_nested_four_valued_status.2.1,
    gate107_high_belief_chooses_risky,
    gate107_threshold_belief_chooses_safe,
    gate107_four_valued_projection_not_control_sufficient⟩

/-!
## Gate-107 interpretation boundary

This is a counterexample to *universal decision sufficiency* of the coarse nested
4PEL status, not a refutation of 4PEL as an epistemic representation. The result
locates the abstraction boundary precisely: thresholded `T/F/B/N` statuses can be
useful qualitative control signals while still discarding quantitative distance
from the threshold that matters to some utility functions.

Accordingly, a richer architecture should distinguish the full quantitative
belief state from its 4PEL projection. Gate 108 can now ask whether epistemic
repair improves a well-defined quantitative potential while the qualitative
status tracks the kind of defect being repaired.
-/

end PEL4
