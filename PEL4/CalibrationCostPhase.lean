import PEL4.ActiveCalibration

namespace PEL4

/-!
# Gate 93: calibration-cost phase transition

Gate 92 showed that calibration is optimal at one concrete price. Gate 93 varies
that price and exhibits the decision boundary where the controller stops buying
meta-information and switches to first-order world sensing.
-/

/-- Net value of calibration at an arbitrary rational cost. -/
def gate93CalibrationNetValue (cost : Rat) : Rat :=
  gate92CalibrationGrossValue - cost

/-- Cost-parametric controller. Ties do not buy calibration. -/
def gate93ChooseAtCost (cost : Rat) : Gate92Action :=
  if gate93CalibrationNetValue cost > gate92WorldSenseNetValue then
    if gate93CalibrationNetValue cost > gate92ActNowValue then .calibrateModel else .actNow
  else if gate92WorldSenseNetValue > gate92ActNowValue then
    .senseWorld
  else
    .actNow

/-- Calibration and world sensing are exactly tied at `13/200`. -/
theorem gate93_boundary_is_indifference :
    gate93CalibrationNetValue ((13 : Rat) / 200) = gate92WorldSenseNetValue := by
  native_decide

/-- The Gate-92 price lies strictly inside the calibration region. -/
theorem gate93_gate92_cost_is_calibration_phase :
    gate93ChooseAtCost gate92CalibrationCost = .calibrateModel := by
  native_decide

/-- Just below the boundary the controller still buys calibration. -/
theorem gate93_below_boundary_calibrates :
    gate93ChooseAtCost ((3 : Rat) / 50) = .calibrateModel := by
  native_decide

/-- At the exact break-even price, the strict controller switches to world sensing. -/
theorem gate93_at_boundary_senses_world :
    gate93ChooseAtCost ((13 : Rat) / 200) = .senseWorld := by
  native_decide

/-- Above the boundary calibration is no longer worth its price. -/
theorem gate93_above_boundary_senses_world :
    gate93ChooseAtCost ((1 : Rat) / 10) = .senseWorld := by
  native_decide

/-- Main Gate-93 theorem: the preferred epistemic action has a genuine cost phase
transition. Meta-information is worth buying only while its price is sufficiently
low relative to the best first-order alternative. -/
theorem gate93_calibration_cost_phase_transition :
    gate93ChooseAtCost gate92CalibrationCost = .calibrateModel ∧
    gate93CalibrationNetValue ((13 : Rat) / 200) = gate92WorldSenseNetValue ∧
    gate93ChooseAtCost ((13 : Rat) / 200) = .senseWorld ∧
    gate93ChooseAtCost ((1 : Rat) / 10) = .senseWorld := by
  exact ⟨gate93_gate92_cost_is_calibration_phase,
    gate93_boundary_is_indifference,
    gate93_at_boundary_senses_world,
    gate93_above_boundary_senses_world⟩

/-!
## Boundary

This is an exact finite phase witness, not a general theorem about all information
cost functions. The strict tie-breaking convention is explicit.
-/

end PEL4
