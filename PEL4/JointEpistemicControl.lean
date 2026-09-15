import PEL4.JointWorldModelBelief

namespace PEL4

/-!
# Gate 90: joint epistemic control

Gate 89 introduced one posterior over world state × sensor model. Gate 90 turns
that joint state into a control-relevant object. Two joint beliefs can agree
exactly about the world while disagreeing about sensor reliability, and this
second-order disagreement alone can reverse the optimal probe.
-/

def gate90DegradedMass (belief : Gate89JointBelief) : Rat :=
  belief.robustDegraded + belief.fragileDegraded

/-- Probe value induced by the model marginal of a joint world-model belief. -/
def gate90ExpectedProbeValue (belief : Gate89JointBelief) (probe : Gate78Probe) : Rat :=
  gate89ReliableMass belief * gate78ProbeValue .reliable probe +
    gate90DegradedMass belief * gate78ProbeValue .degraded probe

/-- Same world marginal as `gate90LowTrust`, but high model trust. -/
def gate90HighTrust : Gate89JointBelief :=
  { robustReliable := (3 : Rat) / 5
    fragileReliable := (1 : Rat) / 5
    robustDegraded := (3 : Rat) / 20
    fragileDegraded := (1 : Rat) / 20 }

/-- Same world marginal as `gate90HighTrust`, but low model trust. -/
def gate90LowTrust : Gate89JointBelief :=
  { robustReliable := (3 : Rat) / 20
    fragileReliable := (1 : Rat) / 20
    robustDegraded := (3 : Rat) / 5
    fragileDegraded := (1 : Rat) / 5 }

/-- Controller inherited from the Gate-78 fragile/safe probe comparison. -/
def gate90ChooseProbe (belief : Gate89JointBelief) : Gate78Probe :=
  if gate90ExpectedProbeValue belief .fragile > gate90ExpectedProbeValue belief .safe then
    .fragile
  else
    .safe

theorem gate90_beliefs_normalized :
    gate89TotalMass gate90HighTrust = 1 ∧ gate89TotalMass gate90LowTrust = 1 := by
  native_decide

theorem gate90_same_world_marginal :
    gate89RobustMass gate90HighTrust = (3 : Rat) / 4 ∧
    gate89RobustMass gate90LowTrust = (3 : Rat) / 4 := by
  native_decide

theorem gate90_different_model_marginals :
    gate89ReliableMass gate90HighTrust = (4 : Rat) / 5 ∧
    gate89ReliableMass gate90LowTrust = (1 : Rat) / 5 := by
  native_decide

theorem gate90_high_trust_values :
    gate90ExpectedProbeValue gate90HighTrust .fragile = (37 : Rat) / 50 ∧
    gate90ExpectedProbeValue gate90HighTrust .safe = (3 : Rat) / 5 := by
  native_decide

theorem gate90_low_trust_values :
    gate90ExpectedProbeValue gate90LowTrust .fragile = (13 : Rat) / 50 ∧
    gate90ExpectedProbeValue gate90LowTrust .safe = (3 : Rat) / 5 := by
  native_decide

theorem gate90_high_trust_chooses_fragile :
    gate90ChooseProbe gate90HighTrust = .fragile := by
  native_decide

theorem gate90_low_trust_chooses_safe :
    gate90ChooseProbe gate90LowTrust = .safe := by
  native_decide

/-- Main Gate-90 theorem: holding first-order world belief fixed does not fix the
optimal action once uncertainty about the evidence-generating model is explicit. -/
theorem gate90_same_world_different_self_trust_changes_control :
    gate89RobustMass gate90HighTrust = gate89RobustMass gate90LowTrust ∧
    gate90ChooseProbe gate90HighTrust = .fragile ∧
    gate90ChooseProbe gate90LowTrust = .safe := by
  native_decide

end PEL4
