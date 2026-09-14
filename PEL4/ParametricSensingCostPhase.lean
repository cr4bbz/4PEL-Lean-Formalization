import PEL4.SequentialBayesianExperimentDesign
namespace PEL4

def gate70StressGrossValue : Rat := (9 : Rat) / 10
def gate70StressNetValue (cost : Rat) : Rat := gate70StressGrossValue - cost
def gate70AliasStopValue : Rat := (1 : Rat) / 2
def gate70CriticalCostHundredths : Nat := 40
inductive Gate70CostPhase where | sampleStress | stop deriving DecidableEq, Repr
def gate70CostPhase (c : Nat) : Gate70CostPhase := if c < gate70CriticalCostHundredths then .sampleStress else .stop
theorem gate70_stress_preferred_iff (c : Nat) : gate70CostPhase c = .sampleStress ↔ c < gate70CriticalCostHundredths := by simp [gate70CostPhase]
theorem gate70_sample_phase_iff (c : Nat) : gate70CostPhase c = .sampleStress ↔ c < gate70CriticalCostHundredths := gate70_stress_preferred_iff c
theorem gate70_stop_phase_iff (c : Nat) : gate70CostPhase c = .stop ↔ ¬ c < gate70CriticalCostHundredths := by simp [gate70CostPhase]
theorem gate70_below_boundary_samples : gate70CostPhase 39 = .sampleStress := by native_decide
theorem gate70_boundary_stops : gate70CostPhase 40 = .stop := by native_decide
theorem gate70_above_boundary_stops : gate70CostPhase 41 = .stop := by native_decide
theorem gate70_boundary_is_indifference : gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue := by native_decide
theorem gate70_gate69_cost_is_sampling_phase : gate70CostPhase 20 = .sampleStress := by native_decide
theorem gate70_recovers_gate69_stress_q : gate70StressNetValue ((1 : Rat) / 5) = sequentialExperimentQ gate69Model 0 gate66AliasedPrior .stressProbe := by native_decide
theorem gate70_parametric_sensing_cost_phase_transition :
    (∀ c : Nat, gate70CostPhase c = .sampleStress ↔ c < gate70CriticalCostHundredths) ∧
    (∀ c : Nat, gate70CostPhase c = .stop ↔ ¬ c < gate70CriticalCostHundredths) ∧
    gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue ∧ gate70CostPhase 20 = .sampleStress := by
  exact ⟨gate70_sample_phase_iff, gate70_stop_phase_iff, gate70_boundary_is_indifference, gate70_gate69_cost_is_sampling_phase⟩
end PEL4
