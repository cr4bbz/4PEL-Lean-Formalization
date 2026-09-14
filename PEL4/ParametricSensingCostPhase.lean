import PEL4.SequentialBayesianExperimentDesign

namespace PEL4

/-!
# Gate 70: parametric sensing-cost phase transition

Gate 69 verified one concrete cost schedule. Gate 70 extracts the stress-probe
tradeoff as a symbolic cost parameter. The gross one-step identification value
of the stress probe at the aliased prior is `9/10`; stopping immediately is
worth `1/2`. Hence the controller changes phase exactly at sensing cost `2/5`.
-/

/-- Gross expected identification value of the alias-breaking stress probe before
paying its sensing cost. Gate 69 instantiated this as `9/10 - 1/5 = 7/10`. -/
def gate70StressGrossValue : Rat := (9 : Rat) / 10

/-- Net one-step value of the stress probe at symbolic sensing cost `cost`. -/
def gate70StressNetValue (cost : Rat) : Rat := gate70StressGrossValue - cost

/-- Immediate stopping value at the unresolved symmetric alias. -/
def gate70AliasStopValue : Rat := (1 : Rat) / 2

inductive Gate70CostPhase where
  | sampleStress
  | stop
  deriving DecidableEq, Repr

/-- Strict improvement is required to buy another sample; ties stop. -/
def gate70CostPhase (cost : Rat) : Gate70CostPhase :=
  if gate70StressNetValue cost > gate70AliasStopValue then
    .sampleStress
  else
    .stop

/-- Exact symbolic phase boundary. -/
theorem gate70_stress_preferred_iff (cost : Rat) :
    gate70StressNetValue cost > gate70AliasStopValue ↔
      cost < (2 : Rat) / 5 := by
  unfold gate70StressNetValue gate70StressGrossValue gate70AliasStopValue
  constructor <;> intro h <;> linarith

/-- Below the critical cost the rational action is to buy the stress probe. -/
theorem gate70_sample_phase_iff (cost : Rat) :
    gate70CostPhase cost = .sampleStress ↔ cost < (2 : Rat) / 5 := by
  simp [gate70CostPhase, gate70_stress_preferred_iff]

/-- At or above the critical cost the rational action is to stop. -/
theorem gate70_stop_phase_iff (cost : Rat) :
    gate70CostPhase cost = .stop ↔ (2 : Rat) / 5 ≤ cost := by
  simp [gate70CostPhase, gate70_stress_preferred_iff, not_lt]

/-- At the boundary the two values coincide exactly, so tie-breaking chooses
stopping. -/
theorem gate70_boundary_is_indifference :
    gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue := by
  norm_num [gate70StressNetValue, gate70StressGrossValue, gate70AliasStopValue]

/-- Gate 69's concrete stress price lies strictly inside the sampling region. -/
theorem gate70_gate69_cost_is_sampling_phase :
    gate70CostPhase ((1 : Rat) / 5) = .sampleStress := by
  norm_num [gate70CostPhase, gate70StressNetValue, gate70StressGrossValue,
    gate70AliasStopValue]

/-- The symbolic net-value expression agrees with the concrete Gate-69 Bellman
Q-value at the declared stress price. -/
theorem gate70_recovers_gate69_stress_q :
    gate70StressNetValue ((1 : Rat) / 5) =
      sequentialExperimentQ gate69Model 0 gate66AliasedPrior .stressProbe := by
  native_decide

/-- Main Gate-70 result: the finite witness contains an exact epistemic action
phase transition at sensing cost `2/5`. -/
theorem gate70_parametric_sensing_cost_phase_transition :
    (∀ cost : Rat,
      gate70CostPhase cost = .sampleStress ↔ cost < (2 : Rat) / 5) ∧
    (∀ cost : Rat,
      gate70CostPhase cost = .stop ↔ (2 : Rat) / 5 ≤ cost) ∧
    gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue ∧
    gate70CostPhase ((1 : Rat) / 5) = .sampleStress := by
  exact ⟨gate70_sample_phase_iff, gate70_stop_phase_iff,
    gate70_boundary_is_indifference, gate70_gate69_cost_is_sampling_phase⟩

/-!
## Boundary

The threshold `2/5` is exact for the Gate-67/Gate-69 alias witness and the
chosen identification utility. Gate 70 does not yet claim that every horizon or
every belief has a single scalar cost boundary. It isolates the first symbolic
phase law that later gates can transport across horizons and policies.
-/

end PEL4
