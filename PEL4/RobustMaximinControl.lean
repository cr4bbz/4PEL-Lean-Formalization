import PEL4.ModelUncertaintyWitness

namespace PEL4

/-!
# Gate 79: robust maximin control

Gate 78 showed that model uncertainty can reverse a probe ranking. Gate 79 turns
that observation into a decision rule: compare the nominal policy with a robust
maximin policy that protects against the worse candidate sensor model.
-/

/-- Nominal control trusts the reliable sensor model. -/
def gate79NominalChoice : Gate78Probe :=
  if gate78ProbeValue .reliable .fragile > gate78ProbeValue .reliable .safe then
    .fragile
  else
    .safe

/-- Worst-case value across the two candidate models in the Gate-78 witness. -/
def gate79WorstCaseValue (probe : Gate78Probe) : Rat :=
  match probe with
  | .fragile => (1 : Rat) / 10
  | .safe => (3 : Rat) / 5

/-- Robust control chooses the probe with the larger guaranteed value. -/
def gate79RobustChoice : Gate78Probe :=
  if gate79WorstCaseValue .fragile > gate79WorstCaseValue .safe then
    .fragile
  else
    .safe

/-- Trusting the nominal model chooses the high-ceiling fragile probe. -/
theorem gate79_nominal_choice_fragile : gate79NominalChoice = .fragile := by
  native_decide

/-- The fragile probe has only `1/10` guaranteed value. -/
theorem gate79_fragile_worst_case :
    gate79WorstCaseValue .fragile = (1 : Rat) / 10 := by
  rfl

/-- The safe probe guarantees `3/5`. -/
theorem gate79_safe_worst_case :
    gate79WorstCaseValue .safe = (3 : Rat) / 5 := by
  rfl

/-- Maximin control therefore switches to the safe probe. -/
theorem gate79_robust_choice_safe : gate79RobustChoice = .safe := by
  native_decide

/-- Main Gate-79 theorem: acknowledging model ambiguity can rationally reverse
an action that was optimal under a trusted nominal model. -/
theorem gate79_robust_control_reverses_nominal_choice :
    gate79NominalChoice = .fragile ∧
    gate79RobustChoice = .safe ∧
    gate79WorstCaseValue .safe > gate79WorstCaseValue .fragile := by
  exact ⟨gate79_nominal_choice_fragile, gate79_robust_choice_safe, by native_decide⟩

/-!
## Gate-79 boundary

The robust rule is deliberately maximin and the ambiguity set contains only two
explicit sensor models. Later work may replace it with Bayesian model averaging,
minimax regret, distributionally robust control, or imprecise probabilities.
-/

end PEL4
