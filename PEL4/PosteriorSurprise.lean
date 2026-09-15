import PEL4.ModelMisspecification

namespace PEL4

/-!
# Gate 99: posterior surprise and model-class doubt

Gate 98 separated posterior normalization from model adequacy. Gate 99 adds a
finite predictive-surprise trigger: an observation that is sufficiently unlikely
under the entire known model class switches the agent from ordinary updating to
explicit doubt about that class.
-/

inductive Gate99Observation where
  | routine
  | anomaly
  deriving DecidableEq, Repr

inductive Gate99MetaMode where
  | normalUpdate
  | modelDoubt
  deriving DecidableEq, Repr

/-- Likelihoods for a diagnostic anomaly under the two known models. -/
def gate99Likelihood (model : Gate98KnownModel) (obs : Gate99Observation) : Rat :=
  match model, obs with
  | .low, .anomaly => (1 : Rat) / 100
  | .high, .anomaly => (1 : Rat) / 50
  | .low, .routine => (99 : Rat) / 100
  | .high, .routine => (49 : Rat) / 50

/-- Predictive evidence under the symmetric closed-class posterior from Gate 98. -/
def gate99PredictiveEvidence (obs : Gate99Observation) : Rat :=
  gate98ForcedPosterior.lowMass * gate99Likelihood .low obs +
    gate98ForcedPosterior.highMass * gate99Likelihood .high obs

def gate99SurpriseThreshold : Rat := (1 : Rat) / 20

def gate99MetaUpdate (obs : Gate99Observation) : Gate99MetaMode :=
  if gate99PredictiveEvidence obs < gate99SurpriseThreshold then
    .modelDoubt
  else
    .normalUpdate

theorem gate99_anomaly_likelihoods_below_threshold :
    gate99Likelihood .low .anomaly < gate99SurpriseThreshold ∧
    gate99Likelihood .high .anomaly < gate99SurpriseThreshold := by
  native_decide

theorem gate99_anomaly_predictive_evidence :
    gate99PredictiveEvidence .anomaly = (3 : Rat) / 200 := by
  native_decide

theorem gate99_routine_predictive_evidence :
    gate99PredictiveEvidence .routine = (197 : Rat) / 200 := by
  native_decide

theorem gate99_routine_stays_in_normal_update :
    gate99MetaUpdate .routine = .normalUpdate := by
  native_decide

theorem gate99_anomaly_triggers_model_doubt :
    gate99MetaUpdate .anomaly = .modelDoubt := by
  native_decide

/-- Main Gate-99 theorem: predictive evidence can distinguish ordinary Bayesian
revision from a meta-level challenge to the model class itself. -/
theorem gate99_surprise_switches_epistemic_regime :
    gate99MetaUpdate .routine = .normalUpdate ∧
    gate99MetaUpdate .anomaly = .modelDoubt ∧
    gate99PredictiveEvidence .anomaly < gate99SurpriseThreshold := by
  native_decide

/-!
## Boundary

The threshold is a concrete finite decision rule, not a universal theorem about
Bayesian model criticism. No logarithmic surprisal is required: the verified
claim concerns low predictive evidence and the resulting regime switch.
-/

end PEL4
