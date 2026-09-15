import PEL4.CalibratedWorldInference

namespace PEL4

/-!
# Gate 93: meta-epistemic dual control

The agent can now spend resources on calibration because calibration changes the
quality of a later world-facing inference. This finite witness treats posterior
world confidence after a positive report as the local epistemic utility.
-/

/-- World-facing confidence after sensing immediately from the uncalibrated prior. -/
def gate93SenseNowValue : Rat :=
  gate90WorldHotMass (gate90PosteriorPositive gate90Prior)

/-- World-facing confidence after calibrating first and then sensing. -/
def gate93CalibrateThenSenseGrossValue : Rat :=
  gate90WorldHotMass gate92CalibratedThenPositive

/-- Explicit cost of the calibration action. -/
def gate93CalibrationCost : Rat := (1 : Rat) / 20

/-- Net local epistemic value of calibration before sensing. -/
def gate93CalibrateThenSenseNetValue : Rat :=
  gate93CalibrateThenSenseGrossValue - gate93CalibrationCost

inductive Gate93Decision where
  | senseNow
  | calibrateThenSense
  deriving DecidableEq, Repr

/-- Choose calibration only when its net value is strictly larger. -/
def gate93ChooseDecision : Gate93Decision :=
  if gate93CalibrateThenSenseNetValue > gate93SenseNowValue then
    .calibrateThenSense
  else
    .senseNow

theorem gate93_sense_now_value : gate93SenseNowValue = (3 : Rat) / 4 := by
  native_decide

theorem gate93_calibrated_gross_value :
    gate93CalibrateThenSenseGrossValue = (93 : Rat) / 110 := by
  native_decide

theorem gate93_calibrated_net_value :
    gate93CalibrateThenSenseNetValue = (35 : Rat) / 44 := by
  native_decide

theorem gate93_calibration_beats_immediate_sensing :
    gate93CalibrateThenSenseNetValue > gate93SenseNowValue := by
  native_decide

theorem gate93_policy_calibrates_first :
    gate93ChooseDecision = .calibrateThenSense := by
  native_decide

/-- Main Gate-93 theorem: model-learning can rationally be selected because it
improves later world-learning enough to repay its explicit cost. -/
theorem gate93_meta_epistemic_dual_control :
    gate93SenseNowValue = (3 : Rat) / 4 ∧
    gate93CalibrateThenSenseNetValue = (35 : Rat) / 44 ∧
    gate93ChooseDecision = .calibrateThenSense := by
  exact ⟨gate93_sense_now_value, gate93_calibrated_net_value,
    gate93_policy_calibrates_first⟩

/-!
## Gate-93 boundary

The utility here is a conditional local witness, not yet a full expected utility
over both positive and negative world observations. The verified structural point
is narrower: once the agent carries uncertainty over its own observation model,
a calibration action can influence the value of a later epistemic action and can
therefore become part of optimal control.
-/

end PEL4
