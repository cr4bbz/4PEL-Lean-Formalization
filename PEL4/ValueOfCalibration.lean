import PEL4.CalibrationStatusWitness

namespace PEL4

/-!
# Gate 81: value of calibration

Gate 80 showed that calibration can defeat overconfidence. Gate 81 makes
calibration an action with a price and compares it with acting immediately under
model ambiguity.
-/

/-- Guaranteed value of acting immediately with the fragile nominal sensor. -/
def gate81ImmediateWorstCase : Rat := (1 : Rat) / 10

/-- Gross decision value available after identifying the sensor regime. -/
def gate81CalibrationGrossValue : Rat := (4 : Rat) / 5

/-- Explicit price of the calibration procedure. -/
def gate81CalibrationCost : Rat := (1 : Rat) / 5

/-- Net value of calibrating before acting. -/
def gate81CalibrationNetValue : Rat :=
  gate81CalibrationGrossValue - gate81CalibrationCost

inductive Gate81Decision where
  | actNow
  | calibrateFirst
  deriving DecidableEq, Repr

/-- Buy calibration exactly when its net value beats immediate robust value. -/
def gate81Choice : Gate81Decision :=
  if gate81CalibrationNetValue > gate81ImmediateWorstCase then
    .calibrateFirst
  else
    .actNow

/-- Calibration retains `3/5` net value after paying its price. -/
theorem gate81_calibration_net_value :
    gate81CalibrationNetValue = (3 : Rat) / 5 := by
  native_decide

/-- Calibration is worth more than immediate action in the ambiguity witness. -/
theorem gate81_calibration_has_positive_information_value :
    gate81CalibrationNetValue > gate81ImmediateWorstCase := by
  native_decide

/-- The local controller therefore calibrates first. -/
theorem gate81_policy_calibrates_first : gate81Choice = .calibrateFirst := by
  native_decide

/-- Main Gate-81 theorem: second-order information about the instrument can be
worth paying for before collecting more first-order evidence about the world. -/
theorem gate81_value_of_calibration :
    gate81CalibrationNetValue = (3 : Rat) / 5 ∧
    gate81CalibrationNetValue > gate81ImmediateWorstCase ∧
    gate81Choice = .calibrateFirst := by
  exact ⟨gate81_calibration_net_value,
    gate81_calibration_has_positive_information_value,
    gate81_policy_calibrates_first⟩

/-!
## Gate-81 boundary

The values are an explicit finite witness rather than a universal calibration
utility theorem. The structural result is that epistemic control can rationally
spend resources on learning the reliability of its own evidence channel.
-/

end PEL4
