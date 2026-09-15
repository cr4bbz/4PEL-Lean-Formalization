import PEL4.ActiveCalibration

namespace PEL4

/-!
# Gate 95: self-correcting policy

A high-trust prior can induce the wrong probe when the true sensor is degraded.
A failed calibration updates the model belief strongly enough to reverse the
policy, and the revised action is objectively better under the true degraded
sensor law.
-/

def gate95OverconfidentBelief : Gate86ModelBelief :=
  { reliableMass := (4 : Rat) / 5
    degradedMass := (1 : Rat) / 5 }

/-- Corrective posterior after a calibration failure. -/
def gate95CorrectedBelief : Gate86ModelBelief :=
  gate87Posterior gate95OverconfidentBelief .fail

theorem gate95_initial_belief_normalized :
    gate95OverconfidentBelief.reliableMass + gate95OverconfidentBelief.degradedMass = 1 := by
  native_decide

theorem gate95_initial_policy_is_fragile :
    gate86ChooseProbe gate95OverconfidentBelief = .fragile := by
  native_decide

theorem gate95_fragile_is_wrong_under_true_degraded_model :
    gate78ProbeValue .degraded .fragile = (1 : Rat) / 10 ∧
    gate78ProbeValue .degraded .safe = (3 : Rat) / 5 ∧
    gate78ProbeValue .degraded .fragile < gate78ProbeValue .degraded .safe := by
  native_decide

theorem gate95_fail_evidence :
    gate87CalibrationEvidence gate95OverconfidentBelief .fail = (6 : Rat) / 25 := by
  native_decide

theorem gate95_corrected_posterior :
    gate95CorrectedBelief.reliableMass = (1 : Rat) / 3 ∧
    gate95CorrectedBelief.degradedMass = (2 : Rat) / 3 := by
  native_decide

theorem gate95_corrected_belief_normalized :
    gate95CorrectedBelief.reliableMass + gate95CorrectedBelief.degradedMass = 1 := by
  native_decide

theorem gate95_corrected_policy_is_safe :
    gate86ChooseProbe gate95CorrectedBelief = .safe := by
  native_decide

/-- Main Gate-95 theorem: calibration evidence repairs a genuinely suboptimal
control choice under the true degraded sensor law. -/
theorem gate95_policy_self_corrects :
    gate86ChooseProbe gate95OverconfidentBelief = .fragile ∧
    gate78ProbeValue .degraded (gate86ChooseProbe gate95OverconfidentBelief) = (1 : Rat) / 10 ∧
    gate86ChooseProbe gate95CorrectedBelief = .safe ∧
    gate78ProbeValue .degraded (gate86ChooseProbe gate95CorrectedBelief) = (3 : Rat) / 5 := by
  native_decide

/-!
## Boundary

This is an exact one-step self-correction witness. It does not establish almost-
sure convergence of model beliefs or policies under repeated observations.
-/

end PEL4
