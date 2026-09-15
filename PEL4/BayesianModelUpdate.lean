import PEL4.BayesianModelBelief

namespace PEL4

/-!
# Gate 87: Bayesian update over sensor models

A calibration result now updates the second-order belief itself. The world state
is held fixed; only the probability assigned to candidate sensor laws changes.
-/

inductive Gate87CalibrationResult where
  | pass
  | fail
  deriving DecidableEq, Repr

/-- Likelihood of a calibration result under a candidate sensor model. -/
def gate87CalibrationLikelihood
    (model : Gate78SensorModel) (result : Gate87CalibrationResult) : Rat :=
  match model, result with
  | .reliable, .pass => (9 : Rat) / 10
  | .reliable, .fail => (1 : Rat) / 10
  | .degraded, .pass => (1 : Rat) / 5
  | .degraded, .fail => (4 : Rat) / 5

/-- Predictive probability of the calibration result under the current model belief. -/
def gate87CalibrationEvidence
    (belief : Gate86ModelBelief) (result : Gate87CalibrationResult) : Rat :=
  belief.reliableMass * gate87CalibrationLikelihood .reliable result +
    belief.degradedMass * gate87CalibrationLikelihood .degraded result

/-- Exact Bayes update for the two-model belief. -/
def gate87Posterior
    (belief : Gate86ModelBelief) (result : Gate87CalibrationResult) : Gate86ModelBelief :=
  let z := gate87CalibrationEvidence belief result
  { reliableMass := belief.reliableMass * gate87CalibrationLikelihood .reliable result / z
    degradedMass := belief.degradedMass * gate87CalibrationLikelihood .degraded result / z }

theorem gate87_skeptical_pass_evidence :
    gate87CalibrationEvidence gate86SkepticalBelief .pass = (11 : Rat) / 20 := by
  native_decide

theorem gate87_skeptical_fail_evidence :
    gate87CalibrationEvidence gate86SkepticalBelief .fail = (9 : Rat) / 20 := by
  native_decide

theorem gate87_pass_posterior :
    (gate87Posterior gate86SkepticalBelief .pass).reliableMass = (9 : Rat) / 11 ∧
    (gate87Posterior gate86SkepticalBelief .pass).degradedMass = (2 : Rat) / 11 := by
  native_decide

theorem gate87_fail_posterior :
    (gate87Posterior gate86SkepticalBelief .fail).reliableMass = (1 : Rat) / 9 ∧
    (gate87Posterior gate86SkepticalBelief .fail).degradedMass = (8 : Rat) / 9 := by
  native_decide

theorem gate87_posteriors_normalized (result : Gate87CalibrationResult) :
    (gate87Posterior gate86SkepticalBelief result).reliableMass +
      (gate87Posterior gate86SkepticalBelief result).degradedMass = 1 := by
  cases result <;> native_decide

/-- Main Gate-87 theorem: calibration evidence can strongly move rational trust
in the observation model in either direction. -/
theorem gate87_bayesian_model_update :
    (gate87Posterior gate86SkepticalBelief .pass).reliableMass = (9 : Rat) / 11 ∧
    (gate87Posterior gate86SkepticalBelief .fail).reliableMass = (1 : Rat) / 9 := by
  exact ⟨gate87_pass_posterior.1, gate87_fail_posterior.1⟩

end PEL4
