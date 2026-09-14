import PEL4.StoppingRegionGeometry

namespace PEL4

/-!
# Gate 72: experiment dominance and pruning

Gate 71 exposed stable stop/sample regions. Gate 72 asks whether some experiments
can be removed from the controller without changing value. At the unresolved
alias, the stress probe weakly dominates both old status sensors at the first two
lookahead depths, and pruning them leaves the Bellman value unchanged.
-/

/-- Decision-local Q-dominance at a belief and remaining horizon. -/
def Gate72QDominates
    (remaining : Nat)
    (belief : BayesianEpistemicBelief Gate47State)
    (better worse : Gate67Experiment) : Prop :=
  sequentialExperimentQ gate69Model remaining belief worse ≤
    sequentialExperimentQ gate69Model remaining belief better

/-- Bellman value if the controller is pruned to stop-or-stress only. -/
def gate72PrunedStressValue
    (remaining : Nat)
    (belief : BayesianEpistemicBelief Gate47State) : Rat :=
  max (gate69Model.stopUtility belief)
    (sequentialExperimentQ gate69Model remaining belief .stressProbe)

/-- Stress dominates the cheap status sensor with one sample available. -/
theorem gate72_stress_dominates_cheap_one_step :
    Gate72QDominates 0 gate66AliasedPrior .stressProbe .statusCheap := by
  unfold Gate72QDominates
  native_decide

/-- Stress dominates the precise status sensor with one sample available. -/
theorem gate72_stress_dominates_precise_one_step :
    Gate72QDominates 0 gate66AliasedPrior .stressProbe .statusPrecise := by
  unfold Gate72QDominates
  native_decide

/-- The same dominance persists when one later sample is priced into Q. -/
theorem gate72_stress_dominates_status_two_step :
    Gate72QDominates 1 gate66AliasedPrior .stressProbe .statusCheap ∧
    Gate72QDominates 1 gate66AliasedPrior .stressProbe .statusPrecise := by
  constructor
  · unfold Gate72QDominates
    native_decide
  · unfold Gate72QDominates
    native_decide

/-- Pruning both old status experiments preserves the one-sample Bellman value. -/
theorem gate72_pruning_preserves_one_sample_value :
    gate72PrunedStressValue 0 gate66AliasedPrior =
      sequentialExperimentValue gate69Model 1 gate66AliasedPrior := by
  native_decide

/-- Pruning also preserves the two-sample Bellman value. -/
theorem gate72_pruning_preserves_two_sample_value :
    gate72PrunedStressValue 1 gate66AliasedPrior =
      sequentialExperimentValue gate69Model 2 gate66AliasedPrior := by
  native_decide

/-- The pruned controller therefore retains the verified value `7/10` at both
lookahead depths. -/
theorem gate72_pruned_value_is_seven_tenths :
    gate72PrunedStressValue 0 gate66AliasedPrior = (7 : Rat) / 10 ∧
    gate72PrunedStressValue 1 gate66AliasedPrior = (7 : Rat) / 10 := by
  constructor <;> native_decide

/-- Main Gate-72 result: locally dominated experiments are dispensable in the
alias witness without any loss of optimal value. -/
theorem gate72_experiment_dominance_and_pruning :
    Gate72QDominates 0 gate66AliasedPrior .stressProbe .statusCheap ∧
    Gate72QDominates 0 gate66AliasedPrior .stressProbe .statusPrecise ∧
    Gate72QDominates 1 gate66AliasedPrior .stressProbe .statusCheap ∧
    Gate72QDominates 1 gate66AliasedPrior .stressProbe .statusPrecise ∧
    gate72PrunedStressValue 0 gate66AliasedPrior =
      sequentialExperimentValue gate69Model 1 gate66AliasedPrior ∧
    gate72PrunedStressValue 1 gate66AliasedPrior =
      sequentialExperimentValue gate69Model 2 gate66AliasedPrior := by
  exact ⟨gate72_stress_dominates_cheap_one_step,
    gate72_stress_dominates_precise_one_step,
    gate72_stress_dominates_status_two_step.1,
    gate72_stress_dominates_status_two_step.2,
    gate72_pruning_preserves_one_sample_value,
    gate72_pruning_preserves_two_sample_value⟩

/-!
## Boundary

Dominance here is local to the declared belief and finite horizons. Gate 72 does
not claim a global Blackwell-order theorem. It establishes the computationally
useful core fact needed later: an experiment can be proven irrelevant to an
optimal epistemic decision and safely removed from the local menu.
-/

end PEL4
