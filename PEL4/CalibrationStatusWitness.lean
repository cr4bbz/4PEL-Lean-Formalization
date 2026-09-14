import PEL4.RobustMaximinControl

namespace PEL4

/-!
# Gate 80: calibration can lower epistemic status

A sensor may report a high nominal confidence even though calibration data show
that its effective evidential support is weaker. In 4PEL this can rationally
move an apparent classical status back into an epistemic gap.
-/

/-- Uncalibrated evidence appears strongly positive. -/
def gate80NominalEvidence : Gate77EvidenceState :=
  { posSupport := (9 : Rat) / 10
    negSupport := (1 : Rat) / 10 }

/-- Calibration discounts the positive channel below the `3/4` threshold. -/
def gate80CalibratedEvidence : Gate77EvidenceState :=
  { posSupport := (3 : Rat) / 5
    negSupport := (2 : Rat) / 5 }

/-- Before calibration the sensor would license strict truth. -/
theorem gate80_nominal_status_true :
    gate77Status gate80NominalEvidence = FDEValue.T := by
  native_decide

/-- After calibration neither side clears the Lockean threshold. -/
theorem gate80_calibrated_status_gap :
    gate77Status gate80CalibratedEvidence = FDEValue.N := by
  native_decide

/-- Main Gate-80 theorem: learning about sensor reliability can rationally reduce
rather than increase one's epistemic confidence. -/
theorem gate80_calibration_can_downgrade_truth_to_gap :
    gate77Status gate80NominalEvidence = FDEValue.T ∧
    gate77Status gate80CalibratedEvidence = FDEValue.N := by
  exact ⟨gate80_nominal_status_true, gate80_calibrated_status_gap⟩

/-!
## Gate-80 boundary

The calibration map is represented by a concrete before/after witness rather
than inferred from data. The formal point is the status transition itself:
second-order evidence about reliability may defeat first-order confidence.
-/

end PEL4
