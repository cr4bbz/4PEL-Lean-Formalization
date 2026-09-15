import PEL4.ModelCalibrationOrthogonality

namespace PEL4

/-!
# Gate 92: calibrated world inference

Gate 91 updated only the sensor-model marginal. Gate 92 feeds that improved
meta-belief back into first-order inference and measures the sharpening of a
subsequent world observation.
-/

/-- Joint posterior after first passing calibration and then receiving a positive
world observation. -/
def gate92CalibratedThenPositive : Gate90JointBelief :=
  gate90PosteriorPositive (gate91PosteriorCalibrationPass gate90Prior)

theorem gate92_joint_posterior :
    gate92CalibratedThenPositive =
      { hotReliable := (81 : Rat) / 110
        hotDegraded := (6 : Rat) / 55
        coolReliable := (9 : Rat) / 110
        coolDegraded := (4 : Rat) / 55 } := by
  native_decide

theorem gate92_world_hot_mass :
    gate90WorldHotMass gate92CalibratedThenPositive = (93 : Rat) / 110 := by
  native_decide

theorem gate92_model_reliable_mass_preserved :
    gate90ModelReliableMass gate92CalibratedThenPositive = (9 : Rat) / 11 := by
  native_decide

theorem gate92_calibration_sharpens_world_inference :
    gate90WorldHotMass gate92CalibratedThenPositive >
      gate90WorldHotMass (gate90PosteriorPositive gate90Prior) := by
  native_decide

/-- Main Gate-92 theorem: calibration can be epistemically orthogonal at the
moment it is performed yet improve the informativeness of the next world-facing
observation. -/
theorem gate92_calibrated_world_inference :
    gate90WorldHotMass gate92CalibratedThenPositive = (93 : Rat) / 110 ∧
    gate90ModelReliableMass gate92CalibratedThenPositive = (9 : Rat) / 11 ∧
    gate90WorldHotMass gate92CalibratedThenPositive >
      gate90WorldHotMass (gate90PosteriorPositive gate90Prior) := by
  exact ⟨gate92_world_hot_mass, gate92_model_reliable_mass_preserved,
    gate92_calibration_sharpens_world_inference⟩

end PEL4
