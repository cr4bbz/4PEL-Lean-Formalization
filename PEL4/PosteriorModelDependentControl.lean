import PEL4.BayesianModelUpdate

namespace PEL4

/-!
# Gate 88: posterior model-dependent control

Gate 87 updates the agent's second-order belief over candidate sensor models.
Gate 88 closes the control loop: the updated model posterior now determines the
next probe choice.
-/

/-- Choose the next probe after observing a calibration result, starting from
Gate 86's skeptical model prior. -/
def gate88ChooseAfterCalibration (result : Gate87CalibrationResult) : Gate78Probe :=
  gate86ChooseProbe (gate87Posterior gate86SkepticalBelief result)

/-- After a successful calibration, posterior trust in the reliable model is
high enough that the high-ceiling fragile probe becomes optimal. -/
theorem gate88_pass_fragile_value :
    gate86ExpectedProbeValue (gate87Posterior gate86SkepticalBelief .pass) .fragile =
      (83 : Rat) / 110 := by
  native_decide

/-- The safe probe keeps its model-independent value after a successful
calibration. -/
theorem gate88_pass_safe_value :
    gate86ExpectedProbeValue (gate87Posterior gate86SkepticalBelief .pass) .safe =
      (3 : Rat) / 5 := by
  native_decide

/-- A passed calibration changes the next Bayes action to the fragile probe. -/
theorem gate88_pass_selects_fragile :
    gate88ChooseAfterCalibration .pass = .fragile := by
  native_decide

/-- After a failed calibration, posterior trust in the reliable model is low and
the fragile probe's expected value collapses. -/
theorem gate88_fail_fragile_value :
    gate86ExpectedProbeValue (gate87Posterior gate86SkepticalBelief .fail) .fragile =
      (17 : Rat) / 90 := by
  native_decide

/-- The safe probe keeps its model-independent value after a failed calibration. -/
theorem gate88_fail_safe_value :
    gate86ExpectedProbeValue (gate87Posterior gate86SkepticalBelief .fail) .safe =
      (3 : Rat) / 5 := by
  native_decide

/-- A failed calibration changes the next Bayes action to the safe probe. -/
theorem gate88_fail_selects_safe :
    gate88ChooseAfterCalibration .fail = .safe := by
  native_decide

/-- Main Gate-88 theorem: calibration evidence changes the model posterior and
thereby reverses the next optimal sensing action. -/
theorem gate88_posterior_model_dependent_control :
    gate88ChooseAfterCalibration .pass = .fragile ∧
    gate88ChooseAfterCalibration .fail = .safe := by
  exact ⟨gate88_pass_selects_fragile, gate88_fail_selects_safe⟩

/-!
## Gate-88 interpretation

The controller is now genuinely second-order adaptive. The same world-level
choice problem produces different optimal actions solely because evidence has
changed the agent's belief about its own observation model.

This is still a finite witness. Gate 89 can lift the construction to a joint
belief over hidden world state and hidden sensor model.
-/

end PEL4
