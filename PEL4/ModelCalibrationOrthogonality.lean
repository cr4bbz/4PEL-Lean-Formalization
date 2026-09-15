import PEL4.JointWorldModelBelief

namespace PEL4

/-!
# Gate 91: calibration orthogonality

A calibration test targets the sensor model rather than the external world. On an
independent prior it can therefore update model trust while leaving the world
marginal exactly unchanged.
-/

def gate91CalibrationPassEvidence (belief : Gate90JointBelief) : Rat :=
  belief.hotReliable * gate87CalibrationLikelihood .reliable .pass +
  belief.hotDegraded * gate87CalibrationLikelihood .degraded .pass +
  belief.coolReliable * gate87CalibrationLikelihood .reliable .pass +
  belief.coolDegraded * gate87CalibrationLikelihood .degraded .pass

/-- Joint posterior after a calibration pass. -/
def gate91PosteriorCalibrationPass (belief : Gate90JointBelief) : Gate90JointBelief :=
  let z := gate91CalibrationPassEvidence belief
  { hotReliable := belief.hotReliable * gate87CalibrationLikelihood .reliable .pass / z
    hotDegraded := belief.hotDegraded * gate87CalibrationLikelihood .degraded .pass / z
    coolReliable := belief.coolReliable * gate87CalibrationLikelihood .reliable .pass / z
    coolDegraded := belief.coolDegraded * gate87CalibrationLikelihood .degraded .pass / z }

theorem gate91_pass_evidence :
    gate91CalibrationPassEvidence gate90Prior = (11 : Rat) / 20 := by
  native_decide

theorem gate91_joint_posterior :
    gate91PosteriorCalibrationPass gate90Prior =
      { hotReliable := (9 : Rat) / 22
        hotDegraded := (1 : Rat) / 11
        coolReliable := (9 : Rat) / 22
        coolDegraded := (1 : Rat) / 11 } := by
  native_decide

theorem gate91_world_marginal_unchanged :
    gate90WorldHotMass (gate91PosteriorCalibrationPass gate90Prior) = (1 : Rat) / 2 := by
  native_decide

theorem gate91_model_marginal_updated :
    gate90ModelReliableMass (gate91PosteriorCalibrationPass gate90Prior) = (9 : Rat) / 11 := by
  native_decide

/-- Main Gate-91 theorem: a pure calibration observation can change second-order
trust without changing first-order belief about the world. -/
theorem gate91_model_calibration_orthogonality :
    gate90WorldHotMass (gate91PosteriorCalibrationPass gate90Prior) = (1 : Rat) / 2 ∧
    gate90ModelReliableMass (gate91PosteriorCalibrationPass gate90Prior) = (9 : Rat) / 11 := by
  exact ⟨gate91_world_marginal_unchanged, gate91_model_marginal_updated⟩

end PEL4
