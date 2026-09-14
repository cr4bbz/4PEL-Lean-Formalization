import PEL4.ParametricSensingCostPhase

namespace PEL4

/-!
# Gate 71: stopping-region geometry

Gate 70 identified a symbolic cost boundary. Gate 71 asks whether the concrete
Gate-69 policy changes merely because another sampling opportunity is available.
For the alias witness it does not: the unresolved prior lies in the sampling
region for both one- and two-step lookahead, while either posterior reached by
the stress probe lies in the stopping region for both lookahead depths.
-/

inductive Gate71Region where
  | sampling
  | stopping
  deriving DecidableEq, Repr

/-- Forget which experiment is sampled and retain only the stop/sample region. -/
def gate71Region
    (remaining : Nat)
    (belief : BayesianEpistemicBelief Gate47State) : Gate71Region :=
  match gate69ChooseDecision remaining belief with
  | .stop => .stopping
  | .sample _ => .sampling

/-- The unresolved alias is in the sampling region with one sample available. -/
theorem gate71_alias_one_step_sampling :
    gate71Region 0 gate66AliasedPrior = .sampling := by
  native_decide

/-- The unresolved alias remains in the sampling region with two samples
available. -/
theorem gate71_alias_two_step_sampling :
    gate71Region 1 gate66AliasedPrior = .sampling := by
  native_decide

/-- After an informative stress outcome, one-step lookahead is already in the
stopping region. -/
theorem gate71_post_stress_one_step_stopping
    (observation : Gate55Observation) :
    gate71Region 0
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      .stopping := by
  cases observation <;> native_decide

/-- Extra lookahead does not revive sensing after the alias has been resolved. -/
theorem gate71_post_stress_two_step_stopping
    (observation : Gate55Observation) :
    gate71Region 1
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      .stopping := by
  cases observation <;> native_decide

/-- The initial Bellman value is horizon-stable across the first two positive
horizons in this witness. -/
theorem gate71_alias_value_horizon_stability :
    sequentialExperimentValue gate69Model 1 gate66AliasedPrior =
        sequentialExperimentValue gate69Model 2 gate66AliasedPrior := by
  rw [gate69_alias_one_sample_value, gate69_alias_two_sample_value]

/-- Likewise, after the stress probe, another available sampling slot does not
raise value above immediate stopping for the first positive horizon. -/
theorem gate71_post_stress_value_is_stop
    (observation : Gate55Observation) :
    sequentialExperimentValue gate69Model 1
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      gate69Model.stopUtility
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) := by
  rw [gate69_post_stress_value observation, gate69_post_stress_stop_value observation]

/-- Main Gate-71 result: the finite witness separates into two policy regions
that are stable under the first nontrivial increase in planning horizon. -/
theorem gate71_stopping_region_geometry :
    gate71Region 0 gate66AliasedPrior = .sampling ∧
    gate71Region 1 gate66AliasedPrior = .sampling ∧
    (∀ observation,
      gate71Region 0
          (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
        .stopping) ∧
    (∀ observation,
      gate71Region 1
          (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
        .stopping) := by
  exact ⟨gate71_alias_one_step_sampling,
    gate71_alias_two_step_sampling,
    gate71_post_stress_one_step_stopping,
    gate71_post_stress_two_step_stopping⟩

/-!
## Boundary

This is finite witness geometry, not yet a theorem that stopping regions are
monotone for every sequential Bayesian model. Such a theorem would require
normalization and regularity assumptions absent from the intentionally lean
Gate-69 structure. Gate 71 instead verifies a robust local fact: more available
lookahead does not alter either side of the alias-resolution decision boundary.
-/

end PEL4
