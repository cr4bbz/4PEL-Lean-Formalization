import PEL4.StochasticEpistemicDecisionProcess

namespace PEL4

/-!
# Gate 51: value of information

Gate 50 introduced stochastic epistemic outcomes. Gate 51 distinguishes the
value of an action from the value of *observing which outcome occurred* before
making a downstream response.

The information source is the Gate-50 exploratory transition. Without observing
the outcome, the agent must commit to one fixed response for both possible
successor states. With information, it may condition its response on the
observed successor state. The resulting improvement is the finite value of
information.
-/

inductive Gate51Response where
  | hold
  | repair
  deriving DecidableEq, Repr

/-- Downstream response utility. Holding is best after robust Recovery; repair
is best after the broken outcome. -/
def gate51ResponseUtility : Gate47State -> Gate51Response -> Nat
  | .robust, .hold => 4
  | .robust, .repair => 1
  | .broken, .hold => 0
  | .broken, .repair => 4
  | _, _ => 0

/-- Expected-utility numerator when the exploratory outcome is *not observed*
and one fixed response must be used across all Gate-50 outcomes. -/
def gate51UninformedValue (response : Gate51Response) : Nat :=
  (gate50Process.outcomes .start .explore).foldl
    (fun total outcome =>
      total + outcome.1 * gate51ResponseUtility outcome.2 response) 0

/-- Best value available without observing the exploratory outcome. -/
def gate51BestUninformedValue : Nat :=
  Nat.max (gate51UninformedValue .hold) (gate51UninformedValue .repair)

/-- State-contingent response after observing the exploratory outcome. -/
def gate51InformedResponse : Gate47State -> Gate51Response
  | .broken => .repair
  | _ => .hold

/-- Expected-utility numerator with observation of the Gate-50 successor state
before choosing the downstream response. -/
def gate51InformedValue : Nat :=
  (gate50Process.outcomes .start .explore).foldl
    (fun total outcome =>
      total + outcome.1 *
        gate51ResponseUtility outcome.2 (gate51InformedResponse outcome.2)) 0

/-- Finite value of information, measured in the common Gate-50 numerator
scale. -/
def gate51ValueOfInformation : Nat :=
  gate51InformedValue - gate51BestUninformedValue

theorem gate51_hold_uninformed_value :
    gate51UninformedValue .hold = 4 := by
  native_decide

theorem gate51_repair_uninformed_value :
    gate51UninformedValue .repair = 5 := by
  native_decide

theorem gate51_best_uninformed_value :
    gate51BestUninformedValue = 5 := by
  native_decide

theorem gate51_informed_value :
    gate51InformedValue = 8 := by
  native_decide

theorem gate51_value_of_information_eq_three :
    gate51ValueOfInformation = 3 := by
  native_decide

/-- Observing the stochastic epistemic outcome before responding has strictly
positive value in the witness. -/
theorem gate51_value_of_information_positive :
    0 < gate51ValueOfInformation := by
  native_decide

/-- Bridge to the destabilization strand: the corresponding exploratory move in
the deterministic Gate-48 control witness immediately leaves Recovery, while
the Gate-50/51 outcome information still has positive downstream decision
value. This is an existential compatibility result, not a universal theorem
that destabilizing evidence is always valuable. -/
theorem gate51_information_can_be_valuable_despite_destabilization :
    ¬ Gate47Recovered (gate48Transition .start .explore) ∧
      0 < gate51ValueOfInformation := by
  exact ⟨gate48_explore_is_immediately_destabilizing,
    gate51_value_of_information_positive⟩

/-- Main Gate-51 theorem: contingent use of the observed exploratory outcome
strictly dominates every fixed uninformed response. -/
theorem gate51_observation_strictly_improves_decision_value :
    gate51InformedValue > gate51BestUninformedValue ∧
      gate51ValueOfInformation = 3 := by
  exact ⟨by native_decide, gate51_value_of_information_eq_three⟩

/-!
## Gate-51 boundary

The value proved here is decision-theoretic value relative to the declared
response utility. It is not Shannon information, mutual information, semantic
truth content, or a universal epistemic utility. The gate proves that the
ability to condition a downstream action on an observed epistemic outcome can
have strictly positive finite value, even alongside a separate verified
short-run destabilization effect.
-/

end PEL4
