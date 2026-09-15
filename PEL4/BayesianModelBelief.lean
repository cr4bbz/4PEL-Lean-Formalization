import PEL4.ModelUncertaintyWitness

namespace PEL4

/-!
# Gate 86: Bayesian belief over sensor models

Gate 78 represented uncertainty by a finite set of possible sensor laws. Gate 86
adds a probability distribution over those laws and lets the controller evaluate
probes by posterior-weighted expected value.
-/

structure Gate86ModelBelief where
  reliableMass : Rat
  degradedMass : Rat
  deriving DecidableEq, Repr

/-- Expected probe value under a belief over the two Gate-78 sensor models. -/
def gate86ExpectedProbeValue (belief : Gate86ModelBelief) (probe : Gate78Probe) : Rat :=
  belief.reliableMass * gate78ProbeValue .reliable probe +
    belief.degradedMass * gate78ProbeValue .degraded probe

/-- A prior that mostly trusts the sensor model. -/
def gate86OptimisticBelief : Gate86ModelBelief :=
  { reliableMass := (3 : Rat) / 4, degradedMass := (1 : Rat) / 4 }

/-- A maximally noncommittal prior over the two sensor models. -/
def gate86SkepticalBelief : Gate86ModelBelief :=
  { reliableMass := (1 : Rat) / 2, degradedMass := (1 : Rat) / 2 }

/-- Local Bayes action: use the fragile probe only when its expected value is
strictly larger; ties go to the safe probe. -/
def gate86ChooseProbe (belief : Gate86ModelBelief) : Gate78Probe :=
  if gate86ExpectedProbeValue belief .fragile > gate86ExpectedProbeValue belief .safe then
    .fragile
  else
    .safe

theorem gate86_optimistic_is_normalized :
    gate86OptimisticBelief.reliableMass + gate86OptimisticBelief.degradedMass = 1 := by
  native_decide

theorem gate86_skeptical_is_normalized :
    gate86SkepticalBelief.reliableMass + gate86SkepticalBelief.degradedMass = 1 := by
  native_decide

theorem gate86_optimistic_values :
    gate86ExpectedProbeValue gate86OptimisticBelief .fragile = (7 : Rat) / 10 ∧
    gate86ExpectedProbeValue gate86OptimisticBelief .safe = (3 : Rat) / 5 := by
  native_decide

theorem gate86_skeptical_values :
    gate86ExpectedProbeValue gate86SkepticalBelief .fragile = (1 : Rat) / 2 ∧
    gate86ExpectedProbeValue gate86SkepticalBelief .safe = (3 : Rat) / 5 := by
  native_decide

theorem gate86_optimistic_selects_fragile :
    gate86ChooseProbe gate86OptimisticBelief = .fragile := by
  native_decide

theorem gate86_skeptical_selects_safe :
    gate86ChooseProbe gate86SkepticalBelief = .safe := by
  native_decide

/-- Main Gate-86 theorem: replacing a set of candidate models by a probability
belief makes sensor-model trust quantitatively decision-relevant. -/
theorem gate86_bayesian_model_belief_changes_policy :
    gate86ChooseProbe gate86OptimisticBelief = .fragile ∧
    gate86ChooseProbe gate86SkepticalBelief = .safe := by
  exact ⟨gate86_optimistic_selects_fragile, gate86_skeptical_selects_safe⟩

end PEL4
