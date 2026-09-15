import PEL4.RepeatedModelLearning

namespace PEL4

/-!
# Gate 90: joint belief over world and sensor model

The agent now represents uncertainty about the external world and uncertainty
about its observation law in one finite joint distribution.
-/

inductive Gate90World where
  | hot
  | cool
  deriving DecidableEq, Repr

structure Gate90JointBelief where
  hotReliable : Rat
  hotDegraded : Rat
  coolReliable : Rat
  coolDegraded : Rat
  deriving DecidableEq, Repr

/-- Independent 1/2 x 1/2 prior over world and sensor model. -/
def gate90Prior : Gate90JointBelief :=
  { hotReliable := (1 : Rat) / 4
    hotDegraded := (1 : Rat) / 4
    coolReliable := (1 : Rat) / 4
    coolDegraded := (1 : Rat) / 4 }

/-- Likelihood of a positive temperature report. -/
def gate90PositiveLikelihood
    (world : Gate90World) (model : Gate78SensorModel) : Rat :=
  match world, model with
  | .hot, .reliable => (9 : Rat) / 10
  | .hot, .degraded => (3 : Rat) / 5
  | .cool, .reliable => (1 : Rat) / 10
  | .cool, .degraded => (2 : Rat) / 5

def gate90PositiveEvidence (belief : Gate90JointBelief) : Rat :=
  belief.hotReliable * gate90PositiveLikelihood .hot .reliable +
  belief.hotDegraded * gate90PositiveLikelihood .hot .degraded +
  belief.coolReliable * gate90PositiveLikelihood .cool .reliable +
  belief.coolDegraded * gate90PositiveLikelihood .cool .degraded

def gate90PosteriorPositive (belief : Gate90JointBelief) : Gate90JointBelief :=
  let z := gate90PositiveEvidence belief
  { hotReliable := belief.hotReliable * gate90PositiveLikelihood .hot .reliable / z
    hotDegraded := belief.hotDegraded * gate90PositiveLikelihood .hot .degraded / z
    coolReliable := belief.coolReliable * gate90PositiveLikelihood .cool .reliable / z
    coolDegraded := belief.coolDegraded * gate90PositiveLikelihood .cool .degraded / z }

def gate90WorldHotMass (belief : Gate90JointBelief) : Rat :=
  belief.hotReliable + belief.hotDegraded

def gate90ModelReliableMass (belief : Gate90JointBelief) : Rat :=
  belief.hotReliable + belief.coolReliable

theorem gate90_prior_normalized :
    gate90Prior.hotReliable + gate90Prior.hotDegraded +
      gate90Prior.coolReliable + gate90Prior.coolDegraded = 1 := by
  native_decide

theorem gate90_positive_evidence_half :
    gate90PositiveEvidence gate90Prior = (1 : Rat) / 2 := by
  native_decide

theorem gate90_positive_joint_posterior :
    gate90PosteriorPositive gate90Prior =
      { hotReliable := (9 : Rat) / 20
        hotDegraded := (3 : Rat) / 10
        coolReliable := (1 : Rat) / 20
        coolDegraded := (1 : Rat) / 5 } := by
  native_decide

theorem gate90_positive_updates_world :
    gate90WorldHotMass (gate90PosteriorPositive gate90Prior) = (3 : Rat) / 4 := by
  native_decide

theorem gate90_positive_does_not_identify_model :
    gate90ModelReliableMass (gate90PosteriorPositive gate90Prior) = (1 : Rat) / 2 := by
  native_decide

/-- Main Gate-90 theorem: one observation can be informative about the world while
remaining exactly uninformative about which sensor model generated it. -/
theorem gate90_joint_world_model_belief :
    gate90WorldHotMass (gate90PosteriorPositive gate90Prior) = (3 : Rat) / 4 ∧
    gate90ModelReliableMass (gate90PosteriorPositive gate90Prior) = (1 : Rat) / 2 := by
  exact ⟨gate90_positive_updates_world, gate90_positive_does_not_identify_model⟩

end PEL4
