import PEL4.SensorModelIdentifiability
import PEL4.CalibrationStatusWitness

namespace PEL4

/-!
# Gate 85: epistemic self-doubt bridge

Gate 85 closes the block by making uncertainty about the sensor model visible in
four-valued epistemic status. Apparent strict truth can rationally fall back to
an evidence gap while the agent questions its instrument, then return to strict
truth or falsity once calibration identifies the regime.
-/

inductive Gate85CalibrationOutcome where
  | reliable
  | inverted
  deriving DecidableEq, Repr

/-- Evidence after the calibration procedure identifies the sensor regime. -/
def gate85ResolvedEvidence
    (outcome : Gate85CalibrationOutcome) : Gate77EvidenceState :=
  match outcome with
  | .reliable =>
      { posSupport := (9 : Rat) / 10, negSupport := (1 : Rat) / 10 }
  | .inverted =>
      { posSupport := (1 : Rat) / 10, negSupport := (9 : Rat) / 10 }

/-- Naive trust in the nominal sensor yields strict truth. -/
theorem gate85_naive_trust_is_true :
    gate77Status gate80NominalEvidence = FDEValue.T := by
  exact gate80_nominal_status_true

/-- Acknowledging unresolved model uncertainty lowers the status to `N`. -/
theorem gate85_self_doubt_opens_gap :
    gate77Status gate80CalibratedEvidence = FDEValue.N := by
  exact gate80_calibrated_status_gap

/-- If calibration validates the sensor, strict truth is restored. -/
theorem gate85_reliable_calibration_restores_true :
    gate77Status (gate85ResolvedEvidence .reliable) = FDEValue.T := by
  native_decide

/-- If calibration finds an inverted sensor, the result becomes strict falsity. -/
theorem gate85_inverted_calibration_restores_false :
    gate77Status (gate85ResolvedEvidence .inverted) = FDEValue.F := by
  native_decide

/-- Every calibration outcome exits the temporary self-doubt gap into a strict
classical status. -/
theorem gate85_calibration_resolves_self_doubt
    (outcome : Gate85CalibrationOutcome) :
    gate77Status (gate85ResolvedEvidence outcome) = FDEValue.T ∨
    gate77Status (gate85ResolvedEvidence outcome) = FDEValue.F := by
  cases outcome <;> native_decide

/-- Main Gate-85 theorem: rational learning about one's own evidence channel can
follow the non-monotone epistemic path `T -> N -> (T or F)`. -/
theorem gate85_epistemic_self_doubt_path :
    gate77Status gate80NominalEvidence = FDEValue.T ∧
    gate77Status gate80CalibratedEvidence = FDEValue.N ∧
    (∀ outcome,
      gate77Status (gate85ResolvedEvidence outcome) = FDEValue.T ∨
      gate77Status (gate85ResolvedEvidence outcome) = FDEValue.F) := by
  exact ⟨gate85_naive_trust_is_true,
    gate85_self_doubt_opens_gap,
    gate85_calibration_resolves_self_doubt⟩

/-!
## Gate-85 boundary

The path is a finite witness, not a general theorem that all rational
self-calibration must pass through `N`. Its conceptual role is sharper: 4PEL can
represent second-order defeat without treating reduced confidence as failure.
The temporary loss of strict status can be the rational consequence of learning
that one's own epistemic instrument is uncertain.
-/

end PEL4
