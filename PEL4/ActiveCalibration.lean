import PEL4.DualValueOfInformation

namespace PEL4

/-!
# Gate 92: active calibration

Calibration becomes an endogenous control action. The agent chooses among acting
now, taking a world-oriented measurement, and paying to calibrate its own sensor
model before acting.
-/

inductive Gate92Action where
  | actNow
  | senseWorld
  | calibrateModel
  deriving DecidableEq, Repr

/-- Immediate control value at the maximally open joint prior. -/
def gate92ActNowValue : Rat :=
  gate90ExpectedProbeValue gate89UniformPrior (gate90ChooseProbe gate89UniformPrior)

/-- A concrete world-sensing option after its sensing cost. -/
def gate92WorldSenseNetValue : Rat := (31 : Rat) / 50

/-- Value of acting optimally after a particular calibration result. -/
def gate92PostCalibrationValue (result : Gate87CalibrationResult) : Rat :=
  let posterior := gate87Posterior gate86SkepticalBelief result
  gate86ExpectedProbeValue posterior (gate86ChooseProbe posterior)

/-- Expected post-calibration control value before paying calibration cost. -/
def gate92CalibrationGrossValue : Rat :=
  gate87CalibrationEvidence gate86SkepticalBelief .pass *
      gate92PostCalibrationValue .pass +
    gate87CalibrationEvidence gate86SkepticalBelief .fail *
      gate92PostCalibrationValue .fail

def gate92CalibrationCost : Rat := (1 : Rat) / 20

def gate92CalibrationNetValue : Rat :=
  gate92CalibrationGrossValue - gate92CalibrationCost

def gate92ActionValue : Gate92Action → Rat
  | .actNow => gate92ActNowValue
  | .senseWorld => gate92WorldSenseNetValue
  | .calibrateModel => gate92CalibrationNetValue

def gate92ChooseAction : Gate92Action :=
  if gate92CalibrationNetValue > gate92WorldSenseNetValue then
    if gate92CalibrationNetValue > gate92ActNowValue then .calibrateModel else .actNow
  else if gate92WorldSenseNetValue > gate92ActNowValue then
    .senseWorld
  else
    .actNow

theorem gate92_act_now_value :
    gate92ActNowValue = (3 : Rat) / 5 := by
  native_decide

theorem gate92_post_calibration_values :
    gate92PostCalibrationValue .pass = (83 : Rat) / 110 ∧
    gate92PostCalibrationValue .fail = (3 : Rat) / 5 := by
  native_decide

theorem gate92_calibration_gross_value :
    gate92CalibrationGrossValue = (137 : Rat) / 200 := by
  native_decide

theorem gate92_calibration_net_value :
    gate92CalibrationNetValue = (127 : Rat) / 200 := by
  native_decide

theorem gate92_calibration_beats_acting_and_world_sensing :
    gate92CalibrationNetValue > gate92ActNowValue ∧
    gate92CalibrationNetValue > gate92WorldSenseNetValue := by
  native_decide

theorem gate92_calibration_cost_is_below_both_break_even_margins :
    gate92CalibrationCost < (17 : Rat) / 200 ∧
    gate92CalibrationCost < (13 : Rat) / 200 := by
  native_decide

/-- Main Gate-92 theorem: self-calibration is selected by the same controller that
could instead act on the world or gather more first-order evidence. -/
theorem gate92_active_controller_chooses_calibration :
    gate92ChooseAction = .calibrateModel := by
  native_decide

end PEL4
