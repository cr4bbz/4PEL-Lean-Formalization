import PEL4.StoppingRegionGeometry

namespace PEL4

def Gate72QDominates
    (remaining : Nat)
    (belief : BayesianEpistemicBelief Gate47State)
    (better worse : Gate67Experiment) : Prop :=
  sequentialExperimentQ gate69Model remaining belief worse ≤
    sequentialExperimentQ gate69Model remaining belief better

def gate72PrunedStressValue
    (remaining : Nat)
    (belief : BayesianEpistemicBelief Gate47State) : Rat :=
  max (gate69Model.stopUtility belief)
    (sequentialExperimentQ gate69Model remaining belief .stressProbe)

theorem gate72_stress_dominates_cheap_one_step :
    Gate72QDominates 0 gate66AliasedPrior .stressProbe .statusCheap := by
  unfold Gate72QDominates
  native_decide

theorem gate72_stress_dominates_precise_one_step :
    Gate72QDominates 0 gate66AliasedPrior .stressProbe .statusPrecise := by
  unfold Gate72QDominates
  native_decide

theorem gate72_stress_dominates_status_two_step :
    Gate72QDominates 1 gate66AliasedPrior .stressProbe .statusCheap ∧
    Gate72QDominates 1 gate66AliasedPrior .stressProbe .statusPrecise := by
  constructor
  · unfold Gate72QDominates
    native_decide
  · unfold Gate72QDominates
    native_decide

theorem gate72_pruning_preserves_one_sample_value :
    gate72PrunedStressValue 0 gate66AliasedPrior =
      sequentialExperimentValue gate69Model 1 gate66AliasedPrior := by
  native_decide

theorem gate72_pruning_preserves_two_sample_value :
    gate72PrunedStressValue 1 gate66AliasedPrior =
      sequentialExperimentValue gate69Model 2 gate66AliasedPrior := by
  native_decide

theorem gate72_pruned_value_is_seven_tenths :
    gate72PrunedStressValue 0 gate66AliasedPrior = (7 : Rat) / 10 ∧
    gate72PrunedStressValue 1 gate66AliasedPrior = (7 : Rat) / 10 := by
  constructor <;> native_decide

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

end PEL4
