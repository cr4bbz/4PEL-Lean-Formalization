import PEL4.BayesianFilterSufficiency

namespace PEL4

/-!
# Gate 62: belief-state Bellman control

Gate 61 established that the current Bayesian posterior is sufficient for future
filtering under a fixed model. Gate 62 turns that posterior into the controller
state of a finite-horizon decision problem. Controller inputs are canonicalized
before evaluation, so accidental list syntax cannot affect value.

The first objective is deliberately narrow: terminal utility is posterior mass
on the Gate-54 truth-certified robust hidden state. This lets us verify a useful
boundary before adding value of information: noisy observation can redistribute
posterior mass without increasing its expectation merely by being observed.
-/

/-- Finite belief-state planning data over a noisy epistemic POMDP. -/
structure FiniteBeliefBellmanModel
    (State Action Observation : Type)
    [DecidableEq State] where
  pomdp : FiniteNoisyEpistemicPOMDP State Action Observation
  support : List State
  actions : List Action
  observations : List Observation
  terminalUtility : BayesianEpistemicBelief State -> Rat

/-- Canonical controller state associated with a raw list representation. -/
def canonicalControllerBelief
    {State Action Observation : Type}
    [DecidableEq State]
    (model : FiniteBeliefBellmanModel State Action Observation)
    (belief : BayesianEpistemicBelief State) : BayesianEpistemicBelief State :=
  canonicalBayesianProfile model.support belief

/-- Canonical noisy posterior used as the next controller state. -/
def beliefControllerUpdate
    {State Action Observation : Type}
    [DecidableEq State]
    (model : FiniteBeliefBellmanModel State Action Observation)
    (belief : BayesianEpistemicBelief State)
    (action : Action)
    (observation : Observation) : BayesianEpistemicBelief State :=
  canonicalControllerBelief model
    (noisyBayesianBeliefUpdate model.pomdp
      (canonicalControllerBelief model belief) action observation)

/-- Finite-horizon Bellman value on canonical Bayesian belief states. Horizon
zero evaluates terminal utility; positive horizons maximize expected continuation
value over the explicit finite action list. -/
def beliefBellmanValue
    {State Action Observation : Type}
    [DecidableEq State]
    (model : FiniteBeliefBellmanModel State Action Observation) :
    Nat -> BayesianEpistemicBelief State -> Rat
  | 0, belief => model.terminalUtility (canonicalControllerBelief model belief)
  | n + 1, belief =>
      (model.actions.map fun action =>
        (model.observations.map fun observation =>
          noisyBayesianObservationProbability model.pomdp
              (canonicalControllerBelief model belief) action observation *
            beliefBellmanValue model n
              (beliefControllerUpdate model belief action observation)).sum).foldl max 0

/-- Bellman action value with `remaining` future decisions after the current
chosen action. -/
def beliefBellmanQ
    {State Action Observation : Type}
    [DecidableEq State]
    (model : FiniteBeliefBellmanModel State Action Observation)
    (remaining : Nat)
    (belief : BayesianEpistemicBelief State)
    (action : Action) : Rat :=
  (model.observations.map fun observation =>
    noisyBayesianObservationProbability model.pomdp
        (canonicalControllerBelief model belief) action observation *
      beliefBellmanValue model remaining
        (beliefControllerUpdate model belief action observation)).sum

/-- Extensionally equal raw beliefs receive exactly the same Bellman value,
because the controller first passes through Gate 59's canonical profile. -/
theorem beliefBellmanValue_eq_of_equivalent
    {State Action Observation : Type}
    [DecidableEq State]
    (model : FiniteBeliefBellmanModel State Action Observation)
    (n : Nat)
    {left right : BayesianEpistemicBelief State}
    (h : BayesianBeliefEquivalent left right) :
    beliefBellmanValue model n left = beliefBellmanValue model n right := by
  have hcanon : canonicalControllerBelief model left =
      canonicalControllerBelief model right := by
    exact canonicalBayesianProfile_eq_of_equivalent model.support h
  induction n with
  | zero => simp [beliefBellmanValue, hcanon]
  | succ n ih =>
      simp only [beliefBellmanValue]
      rw [hcanon]

/-- Gate-62 terminal objective: posterior mass on the bridge-certified robust
hidden state. This is a truth-calibration witness objective, not a general
identity between probability and truth. -/
def gate62TruthMass (belief : BayesianEpistemicBelief Gate47State) : Rat :=
  bayesianWeightAt belief .robust

/-- Belief-state controller for the Gate-60 noisy POMDP. -/
def gate62Model :
    FiniteBeliefBellmanModel Gate47State Gate48Action Gate55Observation where
  pomdp := gate60NoisyPOMDP
  support := gate61Support
  actions := [.exploit, .explore]
  observations := [.recovery, .nonRecovery]
  terminalUtility := gate62TruthMass

/-- Gate 59's duplicate and merged certainty representations have identical
controller value. -/
theorem gate62_syntax_invariant_value :
    beliefBellmanValue gate62Model 2 gate59DuplicatedRobustBelief =
      beliefBellmanValue gate62Model 2 gate59CanonicalRobustBelief := by
  exact beliefBellmanValue_eq_of_equivalent gate62Model 2
    gate59_duplicate_and_canonical_equivalent

/-- Under the symmetric aliased Recovery belief, exploiting for one observation
leaves expected robust posterior mass at one half. -/
theorem gate62_exploit_one_step_truth_mass :
    beliefBellmanQ gate62Model 0 gate57AliasedRecoveryBelief .exploit =
      (1 : Rat) / 2 := by
  native_decide

/-- Exploration also leaves expected robust posterior mass at one half. The
observation changes what the agent knows, but a linear posterior-truth objective
alone does not manufacture expected truth mass. -/
theorem gate62_explore_one_step_truth_mass :
    beliefBellmanQ gate62Model 0 gate57AliasedRecoveryBelief .explore =
      (1 : Rat) / 2 := by
  native_decide

/-- The one-step Bellman value is therefore one half. -/
theorem gate62_one_step_bellman_value :
    beliefBellmanValue gate62Model 1 gate57AliasedRecoveryBelief =
      (1 : Rat) / 2 := by
  native_decide

/-- Main Gate-62 result: Bellman control is well-defined on canonical epistemic
belief states, and pure observation under the linear robust-state objective does
not by itself create expected truth mass. This boundary motivates Gate 63,
where information acquires value through observation-contingent action. -/
theorem gate62_belief_bellman_and_martingale_boundary :
    beliefBellmanQ gate62Model 0 gate57AliasedRecoveryBelief .exploit =
        (1 : Rat) / 2 ∧
    beliefBellmanQ gate62Model 0 gate57AliasedRecoveryBelief .explore =
        (1 : Rat) / 2 ∧
    beliefBellmanValue gate62Model 1 gate57AliasedRecoveryBelief =
        (1 : Rat) / 2 ∧
    beliefBellmanValue gate62Model 2 gate59DuplicatedRobustBelief =
        beliefBellmanValue gate62Model 2 gate59CanonicalRobustBelief := by
  exact ⟨gate62_exploit_one_step_truth_mass,
    gate62_explore_one_step_truth_mass,
    gate62_one_step_bellman_value,
    gate62_syntax_invariant_value⟩

/-!
## Gate-62 boundary

The result is finite-horizon control on a fixed, known noisy POMDP. The terminal
objective is linear posterior mass on one bridge-certified state. The equal
one-step values are a concrete finite witness of the posterior-expectation
boundary, not yet a general martingale theorem. Information can still have
positive decision value once future actions may depend on the observation; that
is Gate 63.
-/

end PEL4
