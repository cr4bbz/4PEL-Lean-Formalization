import PEL4.BeliefStateBellmanControl

namespace PEL4

/-!
# Gate 63: noisy value of information

Gate 62 showed a finite posterior-expectation boundary: under a linear objective
that simply reads posterior mass on `.robust`, observing the noisy signal does
not create expected truth mass. Gate 63 adds a downstream response menu. The
signal can then have strictly positive decision value because different
posteriors rationally select different responses.
-/

inductive Gate63Response where
  | hold
  | repair
  deriving DecidableEq, Repr

/-- Declared downstream utility for the finite witness. `hold` is best if the
hidden state is robust; `repair` is best if it is destabilized. Values for other
states are irrelevant to this witness and set to zero. -/
def gate63ResponsePayoff (state : Gate47State) (response : Gate63Response) : Rat :=
  match state, response with
  | .robust, .hold => 10
  | .robust, .repair => 4
  | .destabilized, .hold => 0
  | .destabilized, .repair => 8
  | _, _ => 0

/-- Expected response utility under a posterior, restricted to the two hidden
states reached by the Gate-60 exploration witness. -/
def gate63ResponseValue
    (belief : BayesianEpistemicBelief Gate47State)
    (response : Gate63Response) : Rat :=
  bayesianWeightAt belief .robust * gate63ResponsePayoff .robust response +
  bayesianWeightAt belief .destabilized *
    gate63ResponsePayoff .destabilized response

/-- Hidden-state prior immediately after exploration but before reading the
noisy sensor. -/
def gate63PredictedBelief : BayesianEpistemicBelief Gate47State :=
  noisyBayesianBeliefPredict gate60NoisyPOMDP
    gate57AliasedRecoveryBelief .explore

/-- Posterior after the noisy Recovery signal. -/
def gate63RecoveryPosterior : BayesianEpistemicBelief Gate47State :=
  noisyBayesianBeliefUpdate gate60NoisyPOMDP
    gate57AliasedRecoveryBelief .explore .recovery

/-- Posterior after the noisy Non-Recovery signal. -/
def gate63NonRecoveryPosterior : BayesianEpistemicBelief Gate47State :=
  noisyBayesianBeliefUpdate gate60NoisyPOMDP
    gate57AliasedRecoveryBelief .explore .nonRecovery

/-- Best fixed response before seeing the signal. -/
def gate63UninformedValue : Rat :=
  max (gate63ResponseValue gate63PredictedBelief .hold)
      (gate63ResponseValue gate63PredictedBelief .repair)

/-- Observation-contingent policy: hold on Recovery, repair on Non-Recovery. -/
def gate63ContingentValue : Rat :=
  noisyBayesianObservationProbability gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .recovery *
      gate63ResponseValue gate63RecoveryPosterior .hold +
  noisyBayesianObservationProbability gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .nonRecovery *
      gate63ResponseValue gate63NonRecoveryPosterior .repair

/-- Decision-theoretic value of the noisy signal in this finite witness. -/
def gate63NoisyVOI : Rat := gate63ContingentValue - gate63UninformedValue

theorem gate63_predicted_belief :
    gate63PredictedBelief =
      [((1 : Rat) / 2, .destabilized), ((1 : Rat) / 2, .robust)] := by
  exact gate60_explore_hidden_prediction

/-- Before observing, holding is worth 5. -/
theorem gate63_uninformed_hold_value :
    gate63ResponseValue gate63PredictedBelief .hold = 5 := by
  native_decide

/-- Before observing, repairing is worth 6 and is therefore the best fixed
response. -/
theorem gate63_uninformed_repair_value :
    gate63ResponseValue gate63PredictedBelief .repair = 6 := by
  native_decide

theorem gate63_best_uninformed_value : gate63UninformedValue = 6 := by
  native_decide

/-- On a Recovery signal, the 9/10 robust posterior makes holding worth 9. -/
theorem gate63_recovery_contingent_value :
    gate63ResponseValue gate63RecoveryPosterior .hold = 9 := by
  native_decide

/-- On a Non-Recovery signal, the 9/10 destabilized posterior makes repair worth
38/5. -/
theorem gate63_nonRecovery_contingent_value :
    gate63ResponseValue gate63NonRecoveryPosterior .repair = (38 : Rat) / 5 := by
  native_decide

/-- Both noisy signals have probability one half in the symmetric witness. -/
theorem gate63_signal_probabilities :
    noisyBayesianObservationProbability gate60NoisyPOMDP
        gate57AliasedRecoveryBelief .explore .recovery = (1 : Rat) / 2 ∧
    noisyBayesianObservationProbability gate60NoisyPOMDP
        gate57AliasedRecoveryBelief .explore .nonRecovery = (1 : Rat) / 2 := by
  constructor <;> native_decide

/-- Expected value when the downstream response may depend on the signal. -/
theorem gate63_contingent_value : gate63ContingentValue = (83 : Rat) / 10 := by
  native_decide

/-- The noisy signal has strictly positive decision value: 83/10 - 6 = 23/10. -/
theorem gate63_noisy_value_of_information :
    gate63NoisyVOI = (23 : Rat) / 10 := by
  native_decide

theorem gate63_noisy_value_of_information_positive :
    gate63NoisyVOI > 0 := by
  native_decide

/-- Main Gate-63 result. Gate 62's expected robust posterior mass remains one
half, yet the noisy observation has strictly positive downstream decision value
because the response can be conditioned on the signal. -/
theorem gate63_information_value_without_expected_truth_mass_gain :
    beliefBellmanQ gate62Model 0 gate57AliasedRecoveryBelief .explore =
        (1 : Rat) / 2 ∧
    gate63UninformedValue = 6 ∧
    gate63ContingentValue = (83 : Rat) / 10 ∧
    gate63NoisyVOI = (23 : Rat) / 10 ∧
    gate63NoisyVOI > 0 := by
  exact ⟨gate62_explore_one_step_truth_mass,
    gate63_best_uninformed_value,
    gate63_contingent_value,
    gate63_noisy_value_of_information,
    gate63_noisy_value_of_information_positive⟩

/-!
## Gate-63 boundary

The positive VOI is relative to the explicitly declared response utilities and
action menu. It does not prove that information is always valuable, that the
payoffs are truth itself, or that noisy observations always improve decisions.
The verified point is narrower and important: unchanged expected linear truth
mass is compatible with strictly positive decision value when later actions may
be observation-contingent.
-/

end PEL4
