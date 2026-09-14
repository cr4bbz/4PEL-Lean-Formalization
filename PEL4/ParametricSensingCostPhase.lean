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

/-- Gross expected identification value of the alias-breaking stress probe before
paying its sensing cost. Gate 69 instantiated this as `9/10 - 1/5 = 7/10`. -/
def gate70StressGrossValue : Rat := (9 : Rat) / 10

/-- Net one-step value of the stress probe at rational sensing cost `cost`. -/
def gate70StressNetValue (cost : Rat) : Rat := gate70StressGrossValue - cost

/-- Immediate stopping value at the unresolved symmetric alias. -/
def gate70AliasStopValue : Rat := (1 : Rat) / 2

/-- Critical sensing price in exact hundredths: `40/100 = 2/5`. -/
def gate70CriticalCostHundredths : Nat := 40

inductive Gate70CostPhase where
  | sampleStress
  | stop
  deriving DecidableEq, Repr

/-- Strict improvement is required to buy another sample; ties stop. Prices are
encoded in hundredths so the exact Gate-69 witness cost `1/5` is `20`. -/
def gate70CostPhase (costHundredths : Nat) : Gate70CostPhase :=
  if costHundredths < gate70CriticalCostHundredths then
    .sampleStress
  else
    .stop

/-- Exact executable phase boundary on the hundredth-price grid. -/
theorem gate70_stress_preferred_iff (costHundredths : Nat) :
    gate70CostPhase costHundredths = .sampleStress ↔
      costHundredths < gate70CriticalCostHundredths := by
  simp [gate70CostPhase]

/-- Alias of the phase law emphasizing the sampling region. -/
theorem gate70_sample_phase_iff (costHundredths : Nat) :
    gate70CostPhase costHundredths = .sampleStress ↔
      costHundredths < gate70CriticalCostHundredths :=
  gate70_stress_preferred_iff costHundredths

/-- At or above the critical point the executable controller stops. -/
theorem gate70_stop_phase_iff (costHundredths : Nat) :
    gate70CostPhase costHundredths = .stop ↔
      ¬ costHundredths < gate70CriticalCostHundredths := by
  simp [gate70CostPhase]

/-- One tick below the boundary remains in the sampling phase. -/
theorem gate70_below_boundary_samples :
    gate70CostPhase 39 = .sampleStress := by
  native_decide

/-- Tie-breaking stops exactly at the boundary. -/
theorem gate70_boundary_stops :
    gate70CostPhase 40 = .stop := by
  native_decide

/-- One tick above the boundary also stops. -/
theorem gate70_above_boundary_stops :
    gate70CostPhase 41 = .stop := by
  native_decide

/-- At rational cost `2/5` the experiment and stop values coincide exactly. -/
theorem gate70_boundary_is_indifference :
    gate70StressNetValue ((2 : Rat) / 5) = gate70AliasStopValue := by
  native_decide

/-- Gate 69's concrete stress price `1/5 = 20/100` lies strictly inside the
sampling region. -/
theorem gate70_gate69_cost_is_sampling_phase :
    gate70CostPhase 20 = .sampleStress := by
  native_decide

/-- The symbolic rational net-value expression agrees with the concrete Gate-69
Bellman Q-value at the declared stress price. -/
theorem gate70_recovers_gate69_stress_q :
    gate70StressNetValue ((1 : Rat) / 5) =
      sequentialExperimentQ gate69Model 0 gate66AliasedPrior .stressProbe := by
  native_decide

/-- Main Gate-70 result: the finite witness contains an exact action phase
transition at 40 hundredths, corresponding to rational cost `2/5`. -/
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

/-!
## Boundary

The threshold `2/5` is exact for the Gate-67/Gate-69 alias witness and the
chosen identification utility. The universal phase classification is represented
on an exact hundredth-price grid; Gate 70 does not claim that every horizon or
every belief has a single scalar cost boundary. It isolates the first executable
phase law that later gates can transport across horizons and policies.
-/

end PEL4
