import PEL4.FiniteEpistemicDecisionProcess

namespace PEL4

/-!
# Gate 50: stochastic epistemic decision process

Gate 49 used deterministic transitions. Gate 50 introduces a separate finite
transition-weight layer. The weights below represent uncertainty over the next
epistemic state induced by an action. They are deliberately distinct from the
probability measure stored *inside* a 4PEL model: transition uncertainty and
internal epistemic probability are different mathematical objects.

To keep the kernel exact and executable, probabilities are represented by
natural weights with a common positive denominator. Non-negativity is therefore
structural, and normalization is an explicit field.
-/

/-- Exact finite stochastic kernel represented by natural weights over a common
denominator. `outcomes s a` is a list of `(weight, nextState)` pairs. -/
structure FiniteWeightedEpistemicProcess (State Action : Type) where
  actions : List Action
  denominator : Nat
  denominator_pos : 0 < denominator
  outcomes : State -> Action -> List (Nat × State)
  normalized : ∀ s a,
    (outcomes s a).foldl (fun total outcome => total + outcome.1) 0 = denominator
  utility : State -> Nat

/-- Weighted expected-utility numerator. Because all actions at a state share
one denominator, comparing these numerators is equivalent to comparing exact
one-step expectations. -/
def weightedExpectedUtilityNumerator
    {State Action : Type}
    (process : FiniteWeightedEpistemicProcess State Action)
    (s : State) (a : Action) : Nat :=
  (process.outcomes s a).foldl
    (fun total outcome => total + outcome.1 * process.utility outcome.2) 0

/-- Gate-50 stochastic outcomes. Exploitation is certain to preserve the
fragile recovered basin at the initial state. Exploration has two equally
weighted outcomes: robust Recovery or failure. Away from the initial state we
reuse the deterministic Gate-48 transition with full weight. -/
def gate50Outcomes : Gate47State -> Gate48Action -> List (Nat × Gate47State)
  | .start, .exploit => [(2, .fragile)]
  | .start, .explore => [(1, .robust), (1, .broken)]
  | s, a => [(2, gate48Transition s a)]

/-- Utility used only for the Gate-50 stochastic witness. -/
def gate50Utility : Gate47State -> Nat
  | .robust => 4
  | .fragile => 1
  | _ => 0

/-- The finite stochastic witness with denominator two. -/
def gate50Process : FiniteWeightedEpistemicProcess Gate47State Gate48Action where
  actions := [.exploit, .explore]
  denominator := 2
  denominator_pos := by decide
  outcomes := gate50Outcomes
  normalized := by
    intro s a
    cases s <;> cases a <;> rfl
  utility := gate50Utility

/-- The exploratory action really is stochastic in the witness: it can end in
robust Recovery or in failure, each with weight one out of two. -/
theorem gate50_explore_has_two_outcomes :
    gate50Process.outcomes .start .explore =
      [(1, .robust), (1, .broken)] := by
  rfl

/-- Exploitation is deterministic at the initial state. -/
theorem gate50_exploit_is_certain_fragile :
    gate50Process.outcomes .start .exploit = [(2, .fragile)] := by
  rfl

/-- Every Gate-50 transition distribution is normalized to the common
transition denominator. -/
theorem gate50_transition_kernel_normalized (s : Gate47State) (a : Gate48Action) :
    (gate50Process.outcomes s a).foldl
      (fun total outcome => total + outcome.1) 0 = 2 := by
  exact gate50Process.normalized s a

/-- Expected-utility numerator for exploiting from the start. -/
theorem gate50_exploit_expected_numerator :
    weightedExpectedUtilityNumerator gate50Process .start .exploit = 2 := by
  native_decide

/-- Expected-utility numerator for exploring from the start. -/
theorem gate50_explore_expected_numerator :
    weightedExpectedUtilityNumerator gate50Process .start .explore = 4 := by
  native_decide

/-- Main Gate-50 result: under an explicit stochastic transition kernel,
exploration has higher expected utility despite carrying a positive-weight
failure outcome. -/
theorem gate50_stochastic_exploration_can_dominate :
    weightedExpectedUtilityNumerator gate50Process .start .explore >
      weightedExpectedUtilityNumerator gate50Process .start .exploit ∧
    gate50Process.outcomes .start .explore =
      [(1, .robust), (1, .broken)] := by
  exact ⟨by native_decide, rfl⟩

/-!
## Gate-50 boundary

The transition weights are not the same thing as a 4PEL model's internal
probability measure. This gate does not identify them, derive one from the
other, or introduce model uncertainty over truth itself. It verifies a finite
normalized stochastic control layer over epistemic states. Gate 51 uses this
layer to define and verify positive value of information.
-/

end PEL4
