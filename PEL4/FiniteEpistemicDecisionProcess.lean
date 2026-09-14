import PEL4.EpistemicExplorationExploitation

namespace PEL4

/-!
# Gate 49: finite epistemic decision process and Bellman recursion

Gate 48 supplied a deterministic controlled epistemic process with two actions,
`exploit` and `explore`. Gate 49 adds an explicit finite-horizon value function.
The purpose of the gate is not merely to restate that exploration is useful, but
to derive the exploratory first action from Bellman recursion itself.

The generic process below is deterministic. Stochastic transition kernels are
reserved for Gate 50.
-/

/-- A finite deterministic epistemic decision process with an explicit action
list, transition function, and natural-number reward. -/
structure FiniteEpistemicDecisionProcess (State Action : Type) where
  actions : List Action
  transition : State -> Action -> State
  reward : State -> Action -> Nat

/-- Finite-horizon Bellman value. Horizon zero has value zero; otherwise the
agent maximizes immediate reward plus the value of the successor state. -/
def finiteBellmanValue
    {State Action : Type}
    (process : FiniteEpistemicDecisionProcess State Action) :
    Nat -> State -> Nat
  | 0, _ => 0
  | n + 1, s =>
      (process.actions.map fun a =>
        process.reward s a +
          finiteBellmanValue process n (process.transition s a)).foldl Nat.max 0

/-- Bellman action value with `remaining` decisions after the current action. -/
def finiteBellmanQ
    {State Action : Type}
    (process : FiniteEpistemicDecisionProcess State Action)
    (remaining : Nat) (s : State) (a : Action) : Nat :=
  process.reward s a +
    finiteBellmanValue process remaining (process.transition s a)

/-- Gate-49 reward: ordinary recovered-fragile states are worth one point,
whereas verified robust Recovery is worth four. Destabilized and integrating
states receive no immediate reward. This is a declared objective, not an
identification of Recovery with truth. -/
def gate49Reward (s : Gate47State) (a : Gate48Action) : Nat :=
  match gate48Transition s a with
  | .fragile => 1
  | .robust => 4
  | _ => 0

/-- The Gate-48 controller as a finite epistemic decision process. -/
def gate49Process : FiniteEpistemicDecisionProcess Gate47State Gate48Action where
  actions := [.exploit, .explore]
  transition := gate48Transition
  reward := gate49Reward

/-- At a one-step horizon the Bellman action value still prefers exploitation. -/
theorem gate49_myopic_q_prefers_exploit :
    finiteBellmanQ gate49Process 0 .start .exploit >
      finiteBellmanQ gate49Process 0 .start .explore := by
  native_decide

/-- With two decisions remaining after the first action, exploration has the
strictly greater action value: it is the only route that can collect the robust
reward by the three-step deadline. -/
theorem gate49_three_step_q_prefers_explore :
    finiteBellmanQ gate49Process 2 .start .explore >
      finiteBellmanQ gate49Process 2 .start .exploit := by
  native_decide

/-- The three-step Bellman value at the initial state is four. -/
theorem gate49_bellman_value_three_start :
    finiteBellmanValue gate49Process 3 .start = 4 := by
  native_decide

/-- The exploratory first action attains the Bellman optimum at horizon three. -/
theorem gate49_explore_attains_bellman_optimum :
    finiteBellmanQ gate49Process 2 .start .explore =
      finiteBellmanValue gate49Process 3 .start := by
  native_decide

/-- The exploitative first action is strictly suboptimal at horizon three. -/
theorem gate49_exploit_is_bellman_suboptimal :
    finiteBellmanQ gate49Process 2 .start .exploit <
      finiteBellmanValue gate49Process 3 .start := by
  native_decide

/-- Main Gate-49 result: extending the planning horizon reverses the locally
preferred action, and Bellman recursion itself selects immediate exploration. -/
theorem gate49_bellman_derives_rational_exploration :
    finiteBellmanQ gate49Process 0 .start .exploit >
        finiteBellmanQ gate49Process 0 .start .explore ∧
    finiteBellmanQ gate49Process 2 .start .explore >
        finiteBellmanQ gate49Process 2 .start .exploit ∧
    finiteBellmanQ gate49Process 2 .start .explore =
        finiteBellmanValue gate49Process 3 .start := by
  exact ⟨gate49_myopic_q_prefers_exploit,
    gate49_three_step_q_prefers_explore,
    gate49_explore_attains_bellman_optimum⟩

/-!
## Gate-49 boundary

This gate verifies finite deterministic dynamic programming. The reward is an
explicit design choice and is not claimed to be the unique epistemically proper
utility. No stochastic kernel, discounting, learning algorithm, unknown model,
or convergence theorem is introduced here. Gate 50 adds a distinct transition
probability layer and keeps it formally separate from the probabilities already
contained inside 4PEL epistemic models.
-/

end PEL4
