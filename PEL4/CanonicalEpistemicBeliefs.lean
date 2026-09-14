import PEL4.GenericBayesianNormalization

namespace PEL4

/-!
# Gate 59: canonical epistemic beliefs

List-based Bayesian beliefs can represent the same distribution in many ways.
Gate 59 introduces extensional belief semantics by summing all weights assigned
to each hidden state. This separates the epistemic state represented by a belief
from the accidental list syntax used to store it.
-/

/-- Total rational weight assigned by a list belief to one hidden state. -/
def bayesianWeightAt
    {State : Type}
    [DecidableEq State]
    (belief : BayesianEpistemicBelief State)
    (state : State) : Rat :=
  ((belief.filter fun item => decide (item.2 = state)).map Prod.fst).sum

/-- Two list beliefs are extensionally equivalent when they assign the same
aggregate weight to every hidden state. -/
def BayesianBeliefEquivalent
    {State : Type}
    [DecidableEq State]
    (left right : BayesianEpistemicBelief State) : Prop :=
  ∀ state, bayesianWeightAt left state = bayesianWeightAt right state

@[refl] theorem BayesianBeliefEquivalent.refl
    {State : Type} [DecidableEq State]
    (belief : BayesianEpistemicBelief State) :
    BayesianBeliefEquivalent belief belief := by
  intro state
  rfl

@[symm] theorem BayesianBeliefEquivalent.symm
    {State : Type} [DecidableEq State]
    {left right : BayesianEpistemicBelief State}
    (h : BayesianBeliefEquivalent left right) :
    BayesianBeliefEquivalent right left := by
  intro state
  exact (h state).symm

@[trans] theorem BayesianBeliefEquivalent.trans
    {State : Type} [DecidableEq State]
    {first second third : BayesianEpistemicBelief State}
    (h₁ : BayesianBeliefEquivalent first second)
    (h₂ : BayesianBeliefEquivalent second third) :
    BayesianBeliefEquivalent first third := by
  intro state
  exact (h₁ state).trans (h₂ state)

/-- Splitting one state's weight into two adjacent entries does not change the
represented Bayesian belief. -/
theorem bayesianBelief_split_same_state_equivalent
    {State : Type}
    [DecidableEq State]
    (a b : Rat)
    (s : State) :
    BayesianBeliefEquivalent
      [(a, s), (b, s)]
      [(a + b, s)] := by
  intro t
  by_cases h : s = t
  · subst t
    simp [bayesianWeightAt]
  · simp [bayesianWeightAt, h]

/-- Conversely, duplicate support entries can be merged without changing the
represented distribution. -/
theorem bayesianBelief_merge_same_state_equivalent
    {State : Type}
    [DecidableEq State]
    (a b : Rat)
    (s : State) :
    BayesianBeliefEquivalent
      [(a + b, s)]
      [(a, s), (b, s)] :=
  (bayesianBelief_split_same_state_equivalent a b s).symm

/-- A canonical profile over an explicit finite support records exactly one
aggregate weight for each listed hidden state. -/
def canonicalBayesianProfile
    {State : Type}
    [DecidableEq State]
    (support : List State)
    (belief : BayesianEpistemicBelief State) : BayesianEpistemicBelief State :=
  support.map fun state => (bayesianWeightAt belief state, state)

/-! ## Concrete Gate-59 witness -/

/-- Syntactically duplicated certainty on the robust hidden state. -/
def gate59DuplicatedRobustBelief : BayesianEpistemicBelief Gate47State :=
  [((1 : Rat) / 2, .robust), ((1 : Rat) / 2, .robust)]

/-- Canonical point belief representing the same distribution. -/
def gate59CanonicalRobustBelief : BayesianEpistemicBelief Gate47State :=
  [((1 : Rat), .robust)]

/-- The two representations are syntactically different. -/
theorem gate59_duplicate_and_canonical_not_equal :
    gate59DuplicatedRobustBelief ≠ gate59CanonicalRobustBelief := by
  native_decide

/-- Nevertheless they encode the same probability distribution over every
Gate-47 hidden state. -/
theorem gate59_duplicate_and_canonical_equivalent :
    BayesianBeliefEquivalent
      gate59DuplicatedRobustBelief gate59CanonicalRobustBelief := by
  exact bayesianBelief_split_same_state_equivalent
    ((1 : Rat) / 2) ((1 : Rat) / 2) Gate47State.robust

/-- Canonicalization on the full Gate-47 support collapses duplicate robust mass
into one state coordinate. Zero coordinates remain explicit to keep support
ordering deterministic. -/
theorem gate59_canonical_profile_of_duplicate :
    canonicalBayesianProfile
      [.start, .fragile, .destabilized, .integrating, .robust]
      gate59DuplicatedRobustBelief =
    [(0, .start), (0, .fragile), (0, .destabilized),
      (0, .integrating), (1, .robust)] := by
  native_decide

/-- Main Gate-59 boundary theorem: list syntax is not epistemic identity. Two
unequal list terms can denote the same Bayesian belief state. -/
theorem gate59_syntax_not_epistemic_identity :
    gate59DuplicatedRobustBelief ≠ gate59CanonicalRobustBelief ∧
    BayesianBeliefEquivalent
      gate59DuplicatedRobustBelief gate59CanonicalRobustBelief := by
  exact ⟨gate59_duplicate_and_canonical_not_equal,
    gate59_duplicate_and_canonical_equivalent⟩

end PEL4
