import PEL4.NoisyEpistemicObservation

namespace PEL4

/-!
# Gate 61: Bayesian filter sufficiency

Gate 39 established state sufficiency for full 4PEL models. Gates 55--60 then
moved to partial observability and noisy Bayesian beliefs over hidden epistemic
states. Gate 61 proves the corresponding filtering principle: once the current
Bayesian belief state is fixed, future filtering depends only on that belief and
on future action/observation inputs, not on the history that produced it.
-/

/-- One controller input consists of a chosen action and the observation
received after that action. -/
abbrev BayesianFilterInput (Action Observation : Type) := Action × Observation

/-- Iterate the noisy Bayesian filter through a finite future input schedule. -/
def noisyBayesianFilterRun
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation) :
    BayesianEpistemicBelief State ->
      List (BayesianFilterInput Action Observation) ->
      BayesianEpistemicBelief State
  | belief, [] => belief
  | belief, (action, observation) :: future =>
      noisyBayesianFilterRun pomdp
        (noisyBayesianBeliefUpdate pomdp belief action observation) future

/-- Same current posterior plus the same future input schedule gives the same
future posterior. -/
theorem noisyBayesianFilter_same_present_same_future
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    {left right : BayesianEpistemicBelief State}
    (future : List (BayesianFilterInput Action Observation))
    (hPresent : left = right) :
    noisyBayesianFilterRun pomdp left future =
      noisyBayesianFilterRun pomdp right future := by
  subst right
  rfl

/-- If two arbitrary histories merge at the same current Bayesian belief, every
common future action/observation schedule produces the same endpoint. -/
theorem noisyBayesianFilter_merged_histories_common_future
    {State Action Observation : Type}
    (pomdp : FiniteNoisyEpistemicPOMDP State Action Observation)
    {start₁ start₂ current : BayesianEpistemicBelief State}
    (history₁ history₂ future : List (BayesianFilterInput Action Observation))
    (h₁ : noisyBayesianFilterRun pomdp start₁ history₁ = current)
    (h₂ : noisyBayesianFilterRun pomdp start₂ history₂ = current) :
    noisyBayesianFilterRun pomdp
        (noisyBayesianFilterRun pomdp start₁ history₁) future =
      noisyBayesianFilterRun pomdp
        (noisyBayesianFilterRun pomdp start₂ history₂) future := by
  rw [h₁, h₂]

/-- Extensional belief equivalence from Gate 59 induces the same canonical
profile on any fixed finite support. -/
theorem canonicalBayesianProfile_eq_of_equivalent
    {State : Type}
    [DecidableEq State]
    (support : List State)
    {left right : BayesianEpistemicBelief State}
    (h : BayesianBeliefEquivalent left right) :
    canonicalBayesianProfile support left =
      canonicalBayesianProfile support right := by
  induction support with
  | nil => rfl
  | cons state rest ih =>
      simp only [canonicalBayesianProfile, List.map_cons]
      rw [h state, ih]

/-- Full finite support used to canonicalize the Gate-47 hidden state space. -/
def gate61Support : List Gate47State :=
  [.start, .fragile, .destabilized, .integrating, .robust]

/-- Gate 59's two syntactically different representations become the same
canonical controller state. -/
theorem gate61_gate59_equivalent_beliefs_same_canonical_state :
    canonicalBayesianProfile gate61Support gate59DuplicatedRobustBelief =
      canonicalBayesianProfile gate61Support gate59CanonicalRobustBelief := by
  exact canonicalBayesianProfile_eq_of_equivalent gate61Support
    gate59_duplicate_and_canonical_equivalent

/-- One noisy observation history reaches Gate 60's Recovery posterior. -/
theorem gate61_history_reaches_recovery_posterior :
    noisyBayesianFilterRun gate60NoisyPOMDP gate57AliasedRecoveryBelief
      [(.explore, .recovery)] =
    [((1 : Rat) / 10, .destabilized), ((9 : Rat) / 10, .robust)] := by
  simpa [noisyBayesianFilterRun] using gate60_recovery_posterior

/-- A history that produced the current posterior and a controller initialized
directly in that posterior have identical futures. This is the concrete
history-compression witness. -/
theorem gate61_history_compression_witness :
    noisyBayesianFilterRun gate60NoisyPOMDP
      (noisyBayesianFilterRun gate60NoisyPOMDP gate57AliasedRecoveryBelief
        [(.explore, .recovery)])
      [(.exploit, .recovery)] =
    noisyBayesianFilterRun gate60NoisyPOMDP
      [((1 : Rat) / 10, .destabilized), ((9 : Rat) / 10, .robust)]
      [(.exploit, .recovery)] := by
  rw [gate61_history_reaches_recovery_posterior]

/-- Main Gate-61 theorem: noisy Bayesian filtering is Markov-sufficient at the
current belief-state level. Different histories that yield the same posterior
require no additional hidden history register for subsequent filtering under a
fixed model and a fixed future action/observation schedule. -/
theorem gate61_bayesian_posterior_is_markov_sufficient :
    (∀ {start₁ start₂ current : BayesianEpistemicBelief Gate47State}
      (history₁ history₂ future :
        List (BayesianFilterInput Gate48Action Gate55Observation)),
      noisyBayesianFilterRun gate60NoisyPOMDP start₁ history₁ = current ->
      noisyBayesianFilterRun gate60NoisyPOMDP start₂ history₂ = current ->
      noisyBayesianFilterRun gate60NoisyPOMDP
          (noisyBayesianFilterRun gate60NoisyPOMDP start₁ history₁) future =
        noisyBayesianFilterRun gate60NoisyPOMDP
          (noisyBayesianFilterRun gate60NoisyPOMDP start₂ history₂) future) ∧
    canonicalBayesianProfile gate61Support gate59DuplicatedRobustBelief =
      canonicalBayesianProfile gate61Support gate59CanonicalRobustBelief := by
  constructor
  · intro start₁ start₂ current history₁ history₂ future h₁ h₂
    exact noisyBayesianFilter_merged_histories_common_future
      gate60NoisyPOMDP history₁ history₂ future h₁ h₂
  · exact gate61_gate59_equivalent_beliefs_same_canonical_state

/-!
## Gate-61 boundary

The sufficiency theorem is conditional on a fixed transition model, fixed noisy
observation kernel, and the actually received future observations. It is a
filtering/Markov sufficiency result, not a claim that the posterior identifies
the true hidden state. Model misspecification, sensor selection, and optimal
control on belief states remain later gates.
-/

end PEL4
