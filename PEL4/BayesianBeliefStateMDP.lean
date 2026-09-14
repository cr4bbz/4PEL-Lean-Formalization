import PEL4.FiniteEpistemicPOMDP

namespace PEL4

/-!
# Gate 57: normalized Bayesian belief-state MDP

Gate 56 introduced a finite epistemic POMDP with exact but unnormalized natural
path weights. Gate 57 lifts that representation to exact rational beliefs. The
belief state is now fully observable to the controller even though the underlying
epistemic state remains hidden.

The construction keeps three probability layers distinct:

1. probability measures internal to a 4PEL epistemic model;
2. stochastic transition probabilities between hidden epistemic states;
3. Bayesian belief probabilities over those hidden epistemic states.

Only layers (2) and (3) are used in this gate.
-/

/-- Exact rational belief over hidden epistemic states. Duplicate states are
still permitted; aggregation is deliberately postponed. -/
abbrev BayesianEpistemicBelief (State : Type) := List (Rat × State)

/-- Total rational mass of a Bayesian belief. -/
def bayesianBeliefMass
    {State : Type}
    (belief : BayesianEpistemicBelief State) : Rat :=
  belief.foldl (fun total item => total + item.1) 0

/-- Normalize a rational belief whenever its total mass is nonzero. A zero-mass
belief is returned unchanged, making impossible observations explicit rather
than inventing posterior mass. -/
def normalizeBayesianBelief
    {State : Type}
    (belief : BayesianEpistemicBelief State) : BayesianEpistemicBelief State :=
  let total := bayesianBeliefMass belief
  if total = 0 then belief
  else belief.map fun item => (item.1 / total, item.2)

/-- Predict a Bayesian belief through the hidden stochastic transition kernel.
Natural transition weights are divided by the process denominator to obtain
exact rational transition probabilities. -/
def bayesianBeliefPredict
    {State Action Observation : Type}
    (pomdp : FiniteWeightedEpistemicPOMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action) : BayesianEpistemicBelief State :=
  belief.flatMap fun prior =>
    (pomdp.dynamics.outcomes prior.2 action).map fun outcome =>
      (prior.1 * ((outcome.1 : Rat) / (pomdp.dynamics.denominator : Rat)),
        outcome.2)

/-- Filter a rational predicted belief by a deterministic observation. -/
def bayesianBeliefCondition
    {State Observation : Type}
    [DecidableEq Observation]
    (observe : State -> Observation)
    (observation : Observation)
    (belief : BayesianEpistemicBelief State) : BayesianEpistemicBelief State :=
  belief.filter fun item => decide (observe item.2 = observation)

/-- Probability mass assigned to one observation after taking an action from a
Bayesian belief state. -/
def bayesianObservationProbability
    {State Action Observation : Type}
    [DecidableEq Observation]
    (pomdp : FiniteWeightedEpistemicPOMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action)
    (observation : Observation) : Rat :=
  bayesianBeliefMass <|
    bayesianBeliefCondition pomdp.observe observation
      (bayesianBeliefPredict pomdp belief action)

/-- Exact Bayesian posterior after an action and received observation. -/
def bayesianBeliefUpdate
    {State Action Observation : Type}
    [DecidableEq Observation]
    (pomdp : FiniteWeightedEpistemicPOMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action)
    (observation : Observation) : BayesianEpistemicBelief State :=
  normalizeBayesianBelief <|
    bayesianBeliefCondition pomdp.observe observation
      (bayesianBeliefPredict pomdp belief action)

/-- A finite belief-state MDP induced by a finite epistemic POMDP and an explicit
finite observation alphabet. Its observable states are Bayesian beliefs. -/
structure FiniteBayesianBeliefStateMDP
    (State Action Observation : Type) where
  pomdp : FiniteWeightedEpistemicPOMDP State Action Observation
  observations : List Observation

/-- Belief-state transition branches. Each observation contributes a branch
weighted by its exact observation probability and labelled with the corresponding
Bayesian posterior. -/
def bayesianBeliefMDPOutcomes
    {State Action Observation : Type}
    [DecidableEq Observation]
    (mdp : FiniteBayesianBeliefStateMDP State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action) : List (Rat × BayesianEpistemicBelief State) :=
  mdp.observations.map fun observation =>
    (bayesianObservationProbability mdp.pomdp belief action observation,
      bayesianBeliefUpdate mdp.pomdp belief action observation)

/-! ## Gate-57 finite witness -/

/-- Exact normalized version of Gate 56's aliased Recovery belief. -/
def gate57AliasedRecoveryBelief : BayesianEpistemicBelief Gate47State :=
  [((1 : Rat) / 2, .fragile), ((1 : Rat) / 2, .robust)]

/-- Belief-state MDP induced by the Gate-56 POMDP. -/
def gate57BeliefStateMDP :
    FiniteBayesianBeliefStateMDP Gate47State Gate48Action Gate55Observation where
  pomdp := gate56POMDP
  observations := [.recovery, .nonRecovery]

/-- The initial Bayesian belief is normalized. -/
theorem gate57_initial_belief_mass_one :
    bayesianBeliefMass gate57AliasedRecoveryBelief = 1 := by
  native_decide

/-- Prediction under exploration preserves total probability mass while moving
the hidden alternatives to `destabilized` and `robust`. -/
theorem gate57_explore_prediction :
    bayesianBeliefPredict gate56POMDP gate57AliasedRecoveryBelief .explore =
      [((1 : Rat) / 2, .destabilized), ((1 : Rat) / 2, .robust)] := by
  native_decide

/-- Under exploration, Recovery and Non-Recovery are equiprobable observations
for the aliased finite witness. -/
theorem gate57_explore_observation_probabilities :
    bayesianObservationProbability gate56POMDP gate57AliasedRecoveryBelief
        .explore .recovery = (1 : Rat) / 2 ∧
    bayesianObservationProbability gate56POMDP gate57AliasedRecoveryBelief
        .explore .nonRecovery = (1 : Rat) / 2 := by
  native_decide

/-- A Recovery observation yields a normalized point posterior on the robust
truth-certified hidden state. -/
theorem gate57_recovery_posterior :
    bayesianBeliefUpdate gate56POMDP gate57AliasedRecoveryBelief
        .explore .recovery = [((1 : Rat), .robust)] := by
  native_decide

/-- A Non-Recovery observation yields the complementary point posterior. -/
theorem gate57_nonRecovery_posterior :
    bayesianBeliefUpdate gate56POMDP gate57AliasedRecoveryBelief
        .explore .nonRecovery = [((1 : Rat), .destabilized)] := by
  native_decide

/-- The induced fully observable belief-state process has two exact branches,
each with probability one half. -/
theorem gate57_belief_mdp_explore_outcomes :
    bayesianBeliefMDPOutcomes gate57BeliefStateMDP
        gate57AliasedRecoveryBelief .explore =
      [((1 : Rat) / 2, [((1 : Rat), .robust)]),
       ((1 : Rat) / 2, [((1 : Rat), .destabilized)])] := by
  native_decide

/-- Observation branches of the finite witness are normalized. -/
theorem gate57_belief_mdp_branch_mass_one :
    (bayesianBeliefMDPOutcomes gate57BeliefStateMDP
      gate57AliasedRecoveryBelief .explore).foldl
        (fun total branch => total + branch.1) 0 = 1 := by
  native_decide

/-- Gate 54's truth bridge survives Bayesian normalization: a Recovery
observation after exploration leaves certainty on the state already certified
as zero-error and truth aligned. -/
theorem gate57_recovery_posterior_truth_certified :
    bayesianBeliefUpdate gate56POMDP gate57AliasedRecoveryBelief
        .explore .recovery = [((1 : Rat), .robust)] ∧
    gate54CalibrationError .robust = 0 ∧
    gate54TruthAligned .robust := by
  exact ⟨gate57_recovery_posterior,
    gate54_robust_state_zero_calibration,
    gate54_robust_state_truth_aligned⟩

/-- Main Gate-57 theorem: the partially observable hidden-state process induces
an exact normalized Markov process on Bayesian beliefs for the finite witness.
The same exploratory action produces two fully observed posterior belief states,
with branch probabilities summing to one. -/
theorem gate57_normalized_belief_state_mdp_witness :
    bayesianBeliefMass gate57AliasedRecoveryBelief = 1 ∧
    bayesianBeliefMDPOutcomes gate57BeliefStateMDP
        gate57AliasedRecoveryBelief .explore =
      [((1 : Rat) / 2, [((1 : Rat), .robust)]),
       ((1 : Rat) / 2, [((1 : Rat), .destabilized)])] ∧
    gate54TruthAligned .robust := by
  exact ⟨gate57_initial_belief_mass_one,
    gate57_belief_mdp_explore_outcomes,
    gate54_robust_state_truth_aligned⟩

/-!
## Gate-57 boundary

Gate 57 verifies an exact normalized Bayesian belief-state MDP for the finite
Gate-56 witness. It does not yet prove generic normalization theorems for every
possible list representation, aggregate duplicate hidden states, introduce a
noisy observation kernel, or optimize policies over arbitrary belief spaces.
The observation channel remains deterministic. The essential verified bridge is
that partial observability at the hidden-state level becomes full observability
at the Bayesian belief-state level.
-/

end PEL4
