import PEL4.MetaValueOfInformation

namespace PEL4

/-!
# Gate 89: repeated Bayesian model learning

Gate 88 gave calibration positive meta-value. Gate 89 studies repeated calibration
and verifies exact accumulation of evidence about the sensor model.
-/

/-- Apply two calibration outcomes sequentially. -/
def gate89Update2
    (first second : Gate87CalibrationResult) : Gate86ModelBelief :=
  gate87Posterior (gate87Posterior gate86SkepticalBelief first) second

theorem gate89_two_passes_strongly_support_reliability :
    (gate89Update2 .pass .pass).reliableMass = (81 : Rat) / 85 := by
  native_decide

theorem gate89_two_failures_strongly_support_degradation :
    (gate89Update2 .fail .fail).reliableMass = (1 : Rat) / 65 := by
  native_decide

theorem gate89_mixed_evidence_posterior :
    (gate89Update2 .pass .fail).reliableMass = (9 : Rat) / 25 := by
  native_decide

theorem gate89_independent_order_agrees :
    gate89Update2 .pass .fail = gate89Update2 .fail .pass := by
  native_decide

theorem gate89_repeated_pass_increases_trust :
    (gate89Update2 .pass .pass).reliableMass >
      (gate87Posterior gate86SkepticalBelief .pass).reliableMass := by
  native_decide

theorem gate89_repeated_fail_decreases_trust :
    (gate89Update2 .fail .fail).reliableMass <
      (gate87Posterior gate86SkepticalBelief .fail).reliableMass := by
  native_decide

/-- Main Gate-89 theorem: independent calibration evidence accumulates coherently,
strengthening repeated agreement while mixed evidence is order-independent. -/
theorem gate89_repeated_model_learning :
    (gate89Update2 .pass .pass).reliableMass = (81 : Rat) / 85 ∧
    (gate89Update2 .fail .fail).reliableMass = (1 : Rat) / 65 ∧
    gate89Update2 .pass .fail = gate89Update2 .fail .pass := by
  exact ⟨gate89_two_passes_strongly_support_reliability,
    gate89_two_failures_strongly_support_degradation,
    gate89_independent_order_agrees⟩

end PEL4
