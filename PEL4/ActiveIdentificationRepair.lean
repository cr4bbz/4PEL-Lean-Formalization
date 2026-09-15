import PEL4.ObservationalAliasingLimit

namespace PEL4

/-!
# Gate 111: active identification restores truth-guaranteeing repair

Gate 110 proved a no-go result for passive self-correction: two hidden worlds can
produce exactly the same available observation while requiring opposite strict
4PEL verdicts. No policy restricted to that aliased observation channel can then
be uniformly correct.

Gate 111 asks whether the failure is permanent. The agent is now allowed to choose
between keeping the old passive channel and performing an active diagnostic
experiment. The diagnostic exposes a new observation dimension that separates the
hidden worlds. A decoder can then recover the correct strict verdict in both
cases, and the repaired nested state is both classically stable and truth-aligned.

This is the self-correction counterpart of the earlier alias-breaking experiment
design result: the novelty here is the explicit bridge from active identification
to truth-guaranteeing epistemic repair after Gate 110's impossibility theorem.
-/

/-- The agent may either keep observing passively or run an alias-breaking
diagnostic. -/
inductive Gate111Experiment where
  | passive
  | disambiguate
  deriving DecidableEq, Repr

/-- The active observation alphabet contains the old aliased reading plus two
world-specific diagnostic signals. -/
inductive Gate111Observation where
  | aliased
  | positiveSignal
  | negativeSignal
  deriving DecidableEq, Repr

/-- The passive experiment preserves Gate 110's alias. The active diagnostic
returns distinct signals in the two hidden worlds. -/
def gate111Observe
    (experiment : Gate111Experiment)
    (world : Gate110HiddenWorld) : Gate111Observation :=
  match experiment, world with
  | .passive, _ => .aliased
  | .disambiguate, .positive => .positiveSignal
  | .disambiguate, .negative => .negativeSignal

/-- Decode diagnostic evidence into a qualitative 4PEL verdict. The old aliased
reading remains unresolved (`N`); the new signals support strict `T` or `F`. -/
def gate111Decode : Gate111Observation → FDEValue
  | .aliased => FDEValue.N
  | .positiveSignal => FDEValue.T
  | .negativeSignal => FDEValue.F

/-- An experiment is truth-guaranteeing when the observation/decoder pipeline
returns the correct strict target in every hidden world. -/
def Gate111TruthGuaranteeing (experiment : Gate111Experiment) : Prop :=
  ∀ world : Gate110HiddenWorld,
    gate111Decode (gate111Observe experiment world) = gate110Target world

/-- Passive observation still aliases the two hidden worlds. -/
theorem gate111_passive_preserves_alias :
    gate111Observe .passive .positive =
      gate111Observe .passive .negative := by
  rfl

/-- The active diagnostic creates genuinely different observations. -/
theorem gate111_diagnostic_breaks_alias :
    gate111Observe .disambiguate .positive ≠
      gate111Observe .disambiguate .negative := by
  native_decide

/-- The old passive channel cannot support a truth-guaranteeing decoder. -/
theorem gate111_passive_not_truth_guaranteeing :
    ¬ Gate111TruthGuaranteeing .passive := by
  intro h
  have hPositive := h Gate110HiddenWorld.positive
  simp [gate111Observe, gate111Decode, gate110Target] at hPositive
  have hNe : FDEValue.N ≠ FDEValue.T := by
    native_decide
  exact hNe hPositive

/-- One active diagnostic is sufficient for exact identification in this finite
witness. -/
theorem gate111_diagnostic_truth_guaranteeing :
    Gate111TruthGuaranteeing .disambiguate := by
  intro world
  cases world <;> rfl

/-- The active experiment is therefore the only truth-guaranteeing member of this
two-experiment menu. -/
theorem gate111_truth_guarantee_iff_disambiguate
    (experiment : Gate111Experiment) :
    Gate111TruthGuaranteeing experiment ↔ experiment = .disambiguate := by
  cases experiment with
  | passive =>
      constructor
      · intro h
        exact False.elim (gate111_passive_not_truth_guaranteeing h)
      · intro h
        cases h
  | disambiguate =>
      constructor
      · intro _
        rfl
      · intro _
        exact gate111_diagnostic_truth_guaranteeing

/-- Reconstruct the nested epistemic state after the active diagnostic. Model
trust remains strict `T`; the world coordinate is supplied by the diagnostic
decoder. -/
def gate111RepairedState (world : Gate110HiddenWorld) : Gate103NestedStatus :=
  { world := gate111Decode (gate111Observe .disambiguate world)
    model := FDEValue.T }

/-- Active identification repairs the first-order coordinate to the correct
strict verdict in every hidden world. -/
theorem gate111_repaired_state_truth_aligned
    (world : Gate110HiddenWorld) :
    (gate111RepairedState world).world = gate110Target world := by
  cases world <;> rfl

/-- The same repaired state is classically stable in Gate 109's sense. -/
theorem gate111_repaired_state_stable
    (world : Gate110HiddenWorld) :
    gate109Stable (gate111RepairedState world) := by
  cases world with
  | positive =>
      change gate109Classical FDEValue.T ∧ gate109Classical FDEValue.T
      exact ⟨Or.inl rfl, Or.inl rfl⟩
  | negative =>
      change gate109Classical FDEValue.F ∧ gate109Classical FDEValue.T
      exact ⟨Or.inr rfl, Or.inl rfl⟩

/-- Gate 110's impossibility and Gate 111's recovery coexist without
contradiction because they quantify over different observation channels. Passive
policies remain impossible to make uniformly correct, while one active
experiment changes the information structure and permits uniform correctness. -/
theorem gate111_active_information_changes_repair_possibility :
    (∀ policy : Gate110RepairPolicy,
      ∃ world : Gate110HiddenWorld, ¬ gate110CorrectAt policy world) ∧
    Gate111TruthGuaranteeing .disambiguate := by
  constructor
  · exact gate110_every_policy_fails_some_aliased_world
  · exact gate111_diagnostic_truth_guaranteeing

/-- Main Gate-111 theorem: active identification breaks the Gate-110 alias and
restores a truth-guaranteeing repair pipeline whose output is classically stable
for every hidden world. -/
theorem gate111_active_identification_restores_truth_guaranteeing_repair :
    gate111Observe .disambiguate .positive ≠
      gate111Observe .disambiguate .negative ∧
    Gate111TruthGuaranteeing .disambiguate ∧
    (∀ world : Gate110HiddenWorld,
      (gate111RepairedState world).world = gate110Target world) ∧
    (∀ world : Gate110HiddenWorld,
      gate109Stable (gate111RepairedState world)) := by
  exact ⟨gate111_diagnostic_breaks_alias,
    gate111_diagnostic_truth_guaranteeing,
    gate111_repaired_state_truth_aligned,
    gate111_repaired_state_stable⟩

/-!
## Gate-111 interpretation boundary

Gate 111 does not claim that every observational alias can be broken. The
alias-breaking diagnostic is explicitly supplied as part of the experiment menu.
The theorem proves the consequence of having access to such an intervention: the
Gate-110 impossibility is channel-relative, not absolute.

The broader structural lesson is now formal. Passive self-repair can be bounded
and terminating yet fail to identify truth; active experiment design can restore
truth-guaranteeing repair exactly when it introduces observations that separate
the hidden target states.

A natural next gate is therefore an experiment-selection problem rather than a
mere existence result: when several probes have different costs and different
separating power, when is it rational to pay for identifiability, and when should
an agent rationally remain unresolved?
-/

end PEL4
