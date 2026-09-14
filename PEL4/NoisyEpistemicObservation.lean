import PEL4.CanonicalEpistemicBeliefs

namespace PEL4

/-!
# Gate 60: noisy epistemic observation

Gates 55--57 used a deterministic Recovery/Non-Recovery observation channel.
Gate 60 replaces that perfect sensor by an exact finite likelihood kernel. A
Recovery signal can now be evidence for a robust truth-certified hidden state
without being an oracle that identifies it with certainty.
-/

/-- A finite epistemic POMDP with stochastic hidden dynamics and a finite noisy
observation kernel represented by exact natural weights. Hidden transition
weights and observation weights have separate denominators. -/
structure FiniteNoisyEpistemicPOMDP
    (State Action Observation : Type) where
  dynamics : FiniteWeightedEpistemicProcess State Action
  observations : List Observation
  observationDenominator : Nat
  observationDenominator_pos : observationDenominator > 0
  observationWeight : State -> Observation -> Nat
  observationNormalized : ∀ state,
    (observations.map (observationWeight state)).sum = observationDenominator

/-- Exact observation likelihood from the finite weight kernel. -/
def noisyObservationLikelihood
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    (state : State)
    (observation : Observation) : Rat :=
  (pomdp.observationWeight state observation : Rat) /
    (pomdp.observationDenominator : Rat)

/-- Hidden-state prediction under the stochastic transition dynamics. -/
def noisyBayesianBeliefPredict
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action) : BayesianEpistemicBelief State :=
  belief.flatMap fun prior =>
    (pomdp.dynamics.outcomes prior.2 action).map fun outcome =>
      (prior.1 * ((outcome.1 : Rat) / (pomdp.dynamics.denominator : Rat)),
        outcome.2)

/-- Multiply each predicted hidden-state mass by the likelihood of the received
observation. This is the unnormalized Bayesian numerator. -/
def noisyBayesianObservationWeight
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    (observation : Observation)
    (predicted : BayesianEpistemicBelief State) : BayesianEpistemicBelief State :=
  predicted.map fun item =>
    (item.1 * noisyObservationLikelihood pomdp item.2 observation, item.2)

/-- Marginal probability of an observation after one action. -/
def noisyBayesianObservationProbability
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action)
    (observation : Observation) : Rat :=
  bayesianBeliefMassSum <|
    noisyBayesianObservationWeight pomdp observation
      (noisyBayesianBeliefPredict pomdp belief action)

/-- One noisy Bayesian filter step: predict, weight by observation likelihood,
then normalize whenever the received observation has nonzero mass. -/
def noisyBayesianBeliefUpdate
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action)
    (observation : Observation) : BayesianEpistemicBelief State :=
  normalizeBayesianBeliefGeneric <|
    noisyBayesianObservationWeight pomdp observation
      (noisyBayesianBeliefPredict pomdp belief action)

/-! ## Gate-60 noisy sensor witness -/

/-- A 90%-reliable version of the coarse Gate-55 Recovery sensor. The reported
signal agrees with the deterministic coarse status with weight 9 and disagrees
with it with weight 1. -/
def gate60ObservationWeight
    (state : Gate47State)
    (observation : Gate55Observation) : Nat :=
  if gate55Observe state = observation then 9 else 1

/-- Finite noisy epistemic POMDP reusing Gate-56 hidden dynamics. -/
def gate60NoisyPOMDP :
    FiniteNoisyEpistemicPOMDP Gate47State Gate48Action Gate55Observation where
  dynamics := gate56Dynamics
  observations := [.recovery, .nonRecovery]
  observationDenominator := 10
  observationDenominator_pos := by decide
  observationWeight := gate60ObservationWeight
  observationNormalized := by
    intro state
    cases state <;> native_decide

/-- The hidden prediction remains Gate 57's fifty-fifty split after exploration. -/
theorem gate60_explore_hidden_prediction :
    noisyBayesianBeliefPredict gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore =
    [((1 : Rat) / 2, .destabilized), ((1 : Rat) / 2, .robust)] := by
  native_decide

/-- A Recovery signal is itself equiprobable in the symmetric prior witness. -/
theorem gate60_recovery_signal_probability :
    noisyBayesianObservationProbability gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .recovery = (1 : Rat) / 2 := by
  native_decide

/-- With noisy sensing, Recovery no longer collapses the posterior to a point.
It leaves 10% probability on the destabilized state and 90% on robust. -/
theorem gate60_recovery_posterior :
    noisyBayesianBeliefUpdate gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .recovery =
    [((1 : Rat) / 10, .destabilized), ((9 : Rat) / 10, .robust)] := by
  native_decide

/-- The complementary Non-Recovery signal reverses those posterior weights. -/
theorem gate60_nonRecovery_posterior :
    noisyBayesianBeliefUpdate gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .nonRecovery =
    [((9 : Rat) / 10, .destabilized), ((1 : Rat) / 10, .robust)] := by
  native_decide

/-- The Recovery posterior is normalized by the generic Gate-58 construction. -/
theorem gate60_recovery_posterior_mass_one :
    bayesianBeliefMassSum
      (noisyBayesianBeliefUpdate gate60NoisyPOMDP
        gate57AliasedRecoveryBelief .explore .recovery) = 1 := by
  native_decide

/-- The robust hidden state's posterior weight is exactly nine tenths after a
Recovery signal. -/
theorem gate60_recovery_signal_robust_weight :
    bayesianWeightAt
      (noisyBayesianBeliefUpdate gate60NoisyPOMDP
        gate57AliasedRecoveryBelief .explore .recovery)
      Gate47State.robust = (9 : Rat) / 10 := by
  native_decide

/-- Noise destroys Gate 57's point-identification property. -/
theorem gate60_recovery_signal_not_oracle :
    noisyBayesianBeliefUpdate gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .recovery ≠
    [((1 : Rat), .robust)] := by
  native_decide

/-- Main Gate-60 result: the same Recovery signal that was perfectly identifying
in Gate 57 becomes probabilistic evidence under a noisy sensor. It raises the
posterior weight of the truth-certified robust state to 9/10, but does not prove
that the hidden state is robust. -/
theorem gate60_recovery_is_evidence_not_oracle :
    bayesianWeightAt
      (noisyBayesianBeliefUpdate gate60NoisyPOMDP
        gate57AliasedRecoveryBelief .explore .recovery)
      Gate47State.robust = (9 : Rat) / 10 ∧
    noisyBayesianBeliefUpdate gate60NoisyPOMDP
      gate57AliasedRecoveryBelief .explore .recovery ≠
      [((1 : Rat), .robust)] ∧
    gate54TruthAligned .robust := by
  exact ⟨gate60_recovery_signal_robust_weight,
    gate60_recovery_signal_not_oracle,
    gate54_robust_state_truth_aligned⟩

/-!
## Gate-60 boundary

The 9/10 reliability is a chosen finite witness, not a universal empirical
calibration claim. Observation noise is now explicit and separate from hidden
transition stochasticity and from probabilities internal to a 4PEL model. This
gate does not yet optimize sensing policies or prove long-run statistical
consistency. It establishes the noisy Bayesian observation layer needed for
those later questions.
-/

end PEL4
