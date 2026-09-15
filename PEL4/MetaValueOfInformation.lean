import PEL4.BayesianModelUpdate

namespace PEL4

/-!
# Gate 88: meta-value of information

Gate 87 can update trust in the sensor model. Gate 88 asks whether buying that
calibration information before choosing a probe can itself be decision-theoretically
valuable.
-/

/-- Value of the locally optimal Gate-86 probe under a model belief. -/
def gate88BestProbeValue (belief : Gate86ModelBelief) : Rat :=
  if gate86ExpectedProbeValue belief .fragile > gate86ExpectedProbeValue belief .safe then
    gate86ExpectedProbeValue belief .fragile
  else
    gate86ExpectedProbeValue belief .safe

/-- Value of acting immediately from the skeptical prior. -/
def gate88ImmediateValue : Rat :=
  gate88BestProbeValue gate86SkepticalBelief

/-- Expected value after observing calibration, before paying its cost. -/
def gate88CalibrationGrossValue : Rat :=
  gate87CalibrationEvidence gate86SkepticalBelief .pass *
      gate88BestProbeValue (gate87Posterior gate86SkepticalBelief .pass) +
    gate87CalibrationEvidence gate86SkepticalBelief .fail *
      gate88BestProbeValue (gate87Posterior gate86SkepticalBelief .fail)

/-- Explicit calibration cost. -/
def gate88CalibrationCost : Rat := (1 : Rat) / 20

/-- Net value of calibrating first. -/
def gate88CalibrationNetValue : Rat :=
  gate88CalibrationGrossValue - gate88CalibrationCost

theorem gate88_immediate_value : gate88ImmediateValue = (3 : Rat) / 5 := by
  native_decide

theorem gate88_pass_best_value :
    gate88BestProbeValue (gate87Posterior gate86SkepticalBelief .pass) = (83 : Rat) / 110 := by
  native_decide

theorem gate88_fail_best_value :
    gate88BestProbeValue (gate87Posterior gate86SkepticalBelief .fail) = (3 : Rat) / 5 := by
  native_decide

theorem gate88_calibration_gross_value :
    gate88CalibrationGrossValue = (137 : Rat) / 200 := by
  native_decide

theorem gate88_calibration_net_value :
    gate88CalibrationNetValue = (127 : Rat) / 200 := by
  native_decide

theorem gate88_calibration_is_worth_buying :
    gate88CalibrationNetValue > gate88ImmediateValue := by
  native_decide

/-- Main Gate-88 theorem: information about the reliability of one's own
measurement process can have strictly positive decision value. -/
theorem gate88_meta_value_of_information :
    gate88CalibrationGrossValue = (137 : Rat) / 200 ∧
    gate88CalibrationNetValue = (127 : Rat) / 200 ∧
    gate88CalibrationNetValue > gate88ImmediateValue := by
  exact ⟨gate88_calibration_gross_value, gate88_calibration_net_value,
    gate88_calibration_is_worth_buying⟩

end PEL4
