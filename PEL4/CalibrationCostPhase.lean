import PEL4.ActiveCalibration

namespace PEL4

/-!
# Gate 93: calibration-cost phase transition

Gate 92 showed that calibration is optimal at one concrete price. Gate 93 varies
that price and exhibits the decision boundary where the controller stops buying
meta-information and switches to first-order world sensing.
-/

def gate93CalibrationNetValue (cost : Rat) : Rat :=
  gate92CalibrationGrossValue - cost

def gate93ChooseAtCost (cost : Rat) : Gate92Action :=
  if gate93CalibrationNetValue cost > gate92WorldSenseNetValue then
    if gate93CalibrationNetValue cost > gate92ActNowValue then .calibrateModel else .actNow
  else if gate92WorldSenseNetValue > gate92ActNowValue then
    .senseWorld
  else
    .actNow

theorem gate93_boundary_is_indifference :
    gate93CalibrationNetValue ((13 : Rat) / 200) = gate92WorldSenseNetValue := by
  native_decide

theorem gate93_gate92_cost_is_calibration_phase :
    gate93ChooseAtCost gate92CalibrationCost = .calibrateModel := by
  native_decide

theorem gate93_below_boundary_calibrates :
    gate93ChooseAtCost ((3 : Rat) / 50) = .calibrateModel := by
  native_decide

theorem gate93_at_boundary_senses_world :
    gate93ChooseAtCost ((13 : Rat) / 200) = .senseWorld := by
  native_decide

theorem gate93_above_boundary_senses_world :
    gate93ChooseAtCost ((1 : Rat) / 10) = .senseWorld := by
  native_decide

theorem gate93_calibration_cost_phase_transition :
    gate93ChooseAtCost gate92CalibrationCost = .calibrateModel ∧
    gate93CalibrationNetValue ((13 : Rat) / 200) = gate92WorldSenseNetValue ∧
    gate93ChooseAtCost ((13 : Rat) / 200) = .senseWorld ∧
    gate93ChooseAtCost ((1 : Rat) / 10) = .senseWorld := by
  exact ⟨gate93_gate92_cost_is_calibration_phase,
    gate93_boundary_is_indifference,
    gate93_at_boundary_senses_world,
    gate93_above_boundary_senses_world⟩

end PEL4
