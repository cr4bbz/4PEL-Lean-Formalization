import PEL4.PartialObservationBoundary

namespace PEL4

/-!
# Gate 56: finite epistemic POMDP and exact belief filtering

Gate 55 proved that the visible Recovery bit is not a sufficient Markov state:
`fragile` and `robust` are observationally aliased even though they differ in
truth/calibration status and react differently to the same action. Gate 56 turns
that boundary into an explicit finite partially observable decision process.

The hidden dynamics are stochastic finite weights, inherited from Gate 50. The
observation channel is deterministic, which is a special case of a POMDP
observation kernel. Beliefs are represented by exact natural path weights. The
belief update first predicts through the hidden transition kernel and then
filters by the received observation.

The weights are intentionally left unnormalized in this gate. They encode exact
relative posterior mass without introducing rational-number normalization or a
general noisy observation kernel yet.
-/

/-- A finite weighted epistemic POMDP with a deterministic observation channel.
The stochastic hidden-state dynamics remain distinct from any probability
measure internal to a 4PEL model. -/
structure FiniteWeightedEpistemicPOMDP
    (State Action Observation : Type) where
  dynamics : FiniteWeightedEpistemicProcess State Action
  observe : State -> Observation

/-- Exact finite belief represented by nonnegative integer weights. Duplicate
hidden states are permitted; this is a path-weight representation rather than a
canonical aggregated distribution. -/
abbrev WeightedEpistemicBelief (State : Type) := List (Nat × State)

/-- Total unnormalized mass of a weighted belief. -/
def weightedBeliefMass
    {State : Type}
    (belief : WeightedEpistemicBelief State) : Nat :=
  belief.foldl (fun total item => total + item.1) 0

/-- Prediction step: multiply prior path weight by hidden transition weight for
every possible successor. -/
def weightedBeliefPredict
    {State Action : Type}
    (process : FiniteWeightedEpistemicProcess State Action)
    (belief : WeightedEpistemicBelief State)
    (action : Action) : WeightedEpistemicBelief State :=
  belief.flatMap fun prior =>
    (process.outcomes prior.2 action).map fun outcome =>
      (prior.1 * outcome.1, outcome.2)

/-- Observation conditioning for a deterministic observation channel. This
filters inconsistent hidden states but deliberately does not renormalize. -/
def weightedBeliefCondition
    {State Observation : Type}
    [DecidableEq Observation]
    (observe : State -> Observation)
    (observation : Observation)
    (belief : WeightedEpistemicBelief State) : WeightedEpistemicBelief State :=
  belief.filter fun item => decide (observe item.2 = observation)

/-- One exact POMDP belief update: hidden-state prediction followed by
observation conditioning. -/
def weightedPOMDPBeliefUpdate
    {State Action Observation : Type}
    [DecidableEq Observation]
    (pomdp : FiniteWeightedEpistemicPOMDP State Action Observation)
    (belief : WeightedEpistemicBelief State)
    (action : Action)
    (observation : Observation) : WeightedEpistemicBelief State :=
  weightedBeliefCondition pomdp.observe observation
    (weightedBeliefPredict pomdp.dynamics belief action)

/-! ## Gate-56 truth-aware finite witness -/

/-- Utility induced by Gate 54's calibration certificate. Zero calibration
error receives one point; positive residual error receives zero. This is still
relative to the explicit Gate-54 bridge, not an unconditional definition of
truth. -/
def gate56TruthCertifiedUtility (s : Gate47State) : Nat :=
  if gate54CalibrationError s = 0 then 1 else 0

/-- Hidden stochastic dynamics reuse Gate 50's normalized transition kernel but
score states with the Gate-54 truth/calibration certificate. -/
def gate56Dynamics : FiniteWeightedEpistemicProcess Gate47State Gate48Action where
  actions := [.exploit, .explore]
  denominator := 2
  denominator_pos := by decide
  outcomes := gate50Outcomes
  normalized := by
    intro s a
    exact gate50Process.normalized s a
  utility := gate56TruthCertifiedUtility

/-- The finite epistemic POMDP: Gate-50 hidden stochastic dynamics plus the
Gate-55 Recovery/Non-Recovery observation channel. -/
def gate56POMDP :
    FiniteWeightedEpistemicPOMDP Gate47State Gate48Action Gate55Observation where
  dynamics := gate56Dynamics
  observe := gate55Observe

/-- Initial belief after seeing only `recovery`: fragile and robust hidden
states remain equally possible in the finite witness. -/
def gate56AliasedRecoveryBelief : WeightedEpistemicBelief Gate47State :=
  [(1, .fragile), (1, .robust)]

/-- The coarse current observation cannot filter the ambiguity between fragile
and robust Recovery. -/
theorem gate56_current_recovery_observation_preserves_ambiguity :
    weightedBeliefCondition gate56POMDP.observe .recovery
        gate56AliasedRecoveryBelief = gate56AliasedRecoveryBelief := by
  rfl

/-- Exploring propagates the two hidden possibilities to two different hidden
successors: destabilized if the state was fragile, robust if it was already
robust. -/
theorem gate56_explore_prediction :
    weightedBeliefPredict gate56POMDP.dynamics gate56AliasedRecoveryBelief
        .explore = [(2, .destabilized), (2, .robust)] := by
  rfl

/-- If the next observation is Recovery, the exact posterior path weight leaves
only the robust hidden state. -/
theorem gate56_recovery_observation_collapses_to_robust :
    weightedPOMDPBeliefUpdate gate56POMDP gate56AliasedRecoveryBelief
        .explore .recovery = [(2, .robust)] := by
  rfl

/-- If the next observation is Non-Recovery, the same exploratory action instead
identifies the destabilized hidden successor. -/
theorem gate56_nonRecovery_observation_collapses_to_destabilized :
    weightedPOMDPBeliefUpdate gate56POMDP gate56AliasedRecoveryBelief
        .explore .nonRecovery = [(2, .destabilized)] := by
  rfl

/-- The prior and predicted masses expose the common-denominator weighting
explicitly. -/
theorem gate56_belief_mass_accounting :
    weightedBeliefMass gate56AliasedRecoveryBelief = 2 ∧
    weightedBeliefMass
      (weightedBeliefPredict gate56POMDP.dynamics
        gate56AliasedRecoveryBelief .explore) = 4 ∧
    weightedBeliefMass
      (weightedPOMDPBeliefUpdate gate56POMDP gate56AliasedRecoveryBelief
        .explore .recovery) = 2 := by
  native_decide

/-- Gate 54 now has operational force under partial observability: after the
informative action and a Recovery observation, the remaining hidden state is
the bridge-certified truth-aligned robust state. -/
theorem gate56_recovery_posterior_truth_certified :
    weightedPOMDPBeliefUpdate gate56POMDP gate56AliasedRecoveryBelief
        .explore .recovery = [(2, .robust)] ∧
    gate54CalibrationError .robust = 0 ∧
    gate54TruthAligned .robust := by
  exact ⟨gate56_recovery_observation_collapses_to_robust,
    gate54_robust_state_zero_calibration,
    gate54_robust_state_truth_aligned⟩

/-- Main Gate-56 result: the same coarse Recovery observation initially hides a
truth-relevant distinction, but an informative epistemic action followed by the
next observation resolves that hidden-state ambiguity in the finite POMDP. -/
theorem gate56_active_observation_resolves_hidden_truth_state :
    gate55Observe .fragile = gate55Observe .robust ∧
    gate54CalibrationError .fragile ≠ gate54CalibrationError .robust ∧
    weightedPOMDPBeliefUpdate gate56POMDP gate56AliasedRecoveryBelief
        .explore .recovery = [(2, .robust)] ∧
    weightedPOMDPBeliefUpdate gate56POMDP gate56AliasedRecoveryBelief
        .explore .nonRecovery = [(2, .destabilized)] ∧
    gate54TruthAligned .robust := by
  exact ⟨gate55_fragile_robust_same_observation,
    gate55_fragile_robust_different_calibration,
    gate56_recovery_observation_collapses_to_robust,
    gate56_nonRecovery_observation_collapses_to_destabilized,
    gate54_robust_state_truth_aligned⟩

/-!
## Gate-56 boundary

This is a genuine finite hidden-state decision process with stochastic hidden
transitions, actions, partial observations, and an explicit belief update. The
observation channel is deterministic, so noisy observation kernels are not yet
formalized. Belief weights are exact but unnormalized and are not aggregated
when duplicate hidden states occur. No RL algorithm or convergence theorem is
claimed. Most importantly, the transition weights remain mathematically
separate from the probability measure stored inside a 4PEL epistemic model.

A natural Gate 57 is a normalized Bayesian belief-state MDP, followed by a noisy
observation kernel and then policy optimization over belief states.
-/

end PEL4
