import PEL4.PosteriorModelDependentControl

namespace PEL4

/-!
# Gate 89: joint world × sensor-model belief

Gate 88 let calibration update a posterior over sensor models and then change the
next probe choice. Gate 89 couples the hidden-world state and the sensor model in
one joint Bayesian state. A single observation can therefore update what the
agent believes about the world and what it believes about its own observation
machinery at the same time.
-/

inductive Gate89World where
  | robust
  | fragile
  deriving DecidableEq, Repr

/-- Four-cell joint belief over world state × Gate-78 sensor model. -/
structure Gate89JointBelief where
  robustReliable : Rat
  fragileReliable : Rat
  robustDegraded : Rat
  fragileDegraded : Rat
  deriving DecidableEq, Repr

/-- Uniform prior: the world state and sensor model both start maximally open. -/
def gate89UniformPrior : Gate89JointBelief :=
  { robustReliable := (1 : Rat) / 4
    fragileReliable := (1 : Rat) / 4
    robustDegraded := (1 : Rat) / 4
    fragileDegraded := (1 : Rat) / 4 }

/-- Likelihood of one positive observation. The reliable sensor is strongly
world-sensitive; the degraded sensor is weak and non-discriminating. -/
def gate89PositiveLikelihood
    (world : Gate89World) (model : Gate78SensorModel) : Rat :=
  match world, model with
  | .robust, .reliable => (9 : Rat) / 10
  | .fragile, .reliable => (1 : Rat) / 10
  | .robust, .degraded => (3 : Rat) / 10
  | .fragile, .degraded => (3 : Rat) / 10

/-- Predictive probability of a positive observation under a joint belief. -/
def gate89PositiveEvidence (belief : Gate89JointBelief) : Rat :=
  belief.robustReliable * gate89PositiveLikelihood .robust .reliable +
  belief.fragileReliable * gate89PositiveLikelihood .fragile .reliable +
  belief.robustDegraded * gate89PositiveLikelihood .robust .degraded +
  belief.fragileDegraded * gate89PositiveLikelihood .fragile .degraded

/-- Exact Bayes update of all four joint cells after a positive observation. -/
def gate89PosteriorPositive (belief : Gate89JointBelief) : Gate89JointBelief :=
  let z := gate89PositiveEvidence belief
  { robustReliable :=
      belief.robustReliable * gate89PositiveLikelihood .robust .reliable / z
    fragileReliable :=
      belief.fragileReliable * gate89PositiveLikelihood .fragile .reliable / z
    robustDegraded :=
      belief.robustDegraded * gate89PositiveLikelihood .robust .degraded / z
    fragileDegraded :=
      belief.fragileDegraded * gate89PositiveLikelihood .fragile .degraded / z }

/-- World marginal for the proposition that the hidden state is robust. -/
def gate89RobustMass (belief : Gate89JointBelief) : Rat :=
  belief.robustReliable + belief.robustDegraded

/-- Model marginal for the proposition that the sensor law is reliable. -/
def gate89ReliableMass (belief : Gate89JointBelief) : Rat :=
  belief.robustReliable + belief.fragileReliable

/-- Total joint mass. -/
def gate89TotalMass (belief : Gate89JointBelief) : Rat :=
  belief.robustReliable + belief.fragileReliable +
    belief.robustDegraded + belief.fragileDegraded

theorem gate89_prior_normalized :
    gate89TotalMass gate89UniformPrior = 1 := by
  native_decide

theorem gate89_prior_marginals :
    gate89RobustMass gate89UniformPrior = (1 : Rat) / 2 ∧
    gate89ReliableMass gate89UniformPrior = (1 : Rat) / 2 := by
  native_decide

theorem gate89_positive_evidence :
    gate89PositiveEvidence gate89UniformPrior = (2 : Rat) / 5 := by
  native_decide

theorem gate89_positive_posterior_cells :
    (gate89PosteriorPositive gate89UniformPrior).robustReliable = (9 : Rat) / 16 ∧
    (gate89PosteriorPositive gate89UniformPrior).fragileReliable = (1 : Rat) / 16 ∧
    (gate89PosteriorPositive gate89UniformPrior).robustDegraded = (3 : Rat) / 16 ∧
    (gate89PosteriorPositive gate89UniformPrior).fragileDegraded = (3 : Rat) / 16 := by
  native_decide

theorem gate89_positive_posterior_normalized :
    gate89TotalMass (gate89PosteriorPositive gate89UniformPrior) = 1 := by
  native_decide

theorem gate89_positive_updates_world_marginal :
    gate89RobustMass (gate89PosteriorPositive gate89UniformPrior) = (3 : Rat) / 4 := by
  native_decide

theorem gate89_positive_updates_model_marginal :
    gate89ReliableMass (gate89PosteriorPositive gate89UniformPrior) = (5 : Rat) / 8 := by
  native_decide

/-- Main Gate-89 theorem: one observation updates both first-order world belief
and second-order trust in the observation model from the same joint posterior. -/
theorem gate89_joint_update_moves_world_and_model :
    gate89RobustMass gate89UniformPrior = (1 : Rat) / 2 ∧
    gate89ReliableMass gate89UniformPrior = (1 : Rat) / 2 ∧
    gate89RobustMass (gate89PosteriorPositive gate89UniformPrior) = (3 : Rat) / 4 ∧
    gate89ReliableMass (gate89PosteriorPositive gate89UniformPrior) = (5 : Rat) / 8 := by
  exact ⟨gate89_prior_marginals.1,
    gate89_prior_marginals.2,
    gate89_positive_updates_world_marginal,
    gate89_positive_updates_model_marginal⟩

/-!
## Gate-89 boundary

This is a finite four-cell witness with one positive observation. It does not yet
prove a generic joint Bayesian filter for arbitrary finite world/model spaces, nor
does it yet feed the joint posterior into a Bellman controller. Those are follow-up
gates.
-/

end PEL4
