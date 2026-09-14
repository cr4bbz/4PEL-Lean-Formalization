import PEL4.SequentialBayesianExperimentDesign

namespace PEL4

/-!
# Gate 70: parametric sensing-cost phase transition

Gate 69 verified one concrete cost schedule. Gate 70 exposes the stress-probe
tradeoff on an exact hundredth-price grid. The gross one-step identification
value of the stress probe at the aliased prior is `9/10`; stopping immediately
is worth `1/2`. The indifference price is therefore `2/5 = 40/100`.

The grid representation keeps the phase theorem executable without adding an
external arithmetic-tactic dependency to the project. The rational equality at
the boundary is verified separately below.
-/

def gate70StressGrossValue : Rat := (9 : Rat) / 10
def gate70StressNetValue (cost : Rat) : Rat := gate70StressGrossValue - cost
def gate70AliasStopValue : Rat := (1 : Rat) / 2
def gate70CriticalCostHundredths : Nat := 40

inductive Gate70CostPhase where
  | sampleStress
  | stop
  deriving DecidableEq, Repr

def gate70CostPhase (costHundredths : Nat) : Gate70CostPhase :=
  if costHundredths < gate70CriticalCostHundredths then .sampleStress else .stop

theorem gate70_stress_preferred_iff (costHundredths : Nat) :
    gate70CostPhase costHundredths = .sampleStress ↔
      costHundredths < gate70CriticalCostHundredths := by
  simp [gate70CostPhase]

theorem gate70_sample_phase_iff (costHundredths : Nat) :
    gate70CostPhase costHundredths = .sampleStress ↔
      costHundredths < gate70CriticalCostHundredths :=
  gate70_stress_preferred_iff costHundredths

theorem gate70_stop_phase_iff (costHundredths : Nat) :
    gate70CostPhase costHundredths = .stop ↔
      ¬ costHundredths < gate70CriticalCostHundredths := by
  simp [gate70CostPhase]

theorem gate70_below_boundary_samples : gate70CostPhase 39 = .sampleStress := by native_decide
theorem gate70_boundary_stops : gate70CostPhase 40 = .stop := by native_decide
theorem gate70_above_boundary_stops : gate70CostPhase 41 = .stop := by native_decide

theorem gate70_boundary_is_indifference :
    gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue := by
  native_decide

theorem gate70_gate69_cost_is_sampling_phase :
    gate70CostPhase 20 = .sampleStress := by
  native_decide

theorem gate70_recovers_gate69_stress_q :
    gate70StressNetValue ((1 : Rat) / 5) =
      sequentialExperimentQ gate69Model 0 gate66AliasedPrior .stressProbe := by
  native_decide

theorem gate70_parametric_sensing_cost_phase_transition :
    (∀ costHundredths : Nat,
      gate70CostPhase costHundredths = .sampleStress ↔
        costHundredths < gate70CriticalCostHundredths) ∧
    (∀ costHundredths : Nat,
      gate70CostPhase costHundredths = .stop ↔
        ¬ costHundredths < gate70CriticalCostHundredths) ∧
    gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue ∧
    gate70CostPhase 20 = .sampleStress := by
  exact ⟨gate70_sample_phase_iff, gate70_stop_phase_iff,
    gate70_boundary_is_indifference, gate70_gate69_cost_is_sampling_phase⟩

end PEL4
