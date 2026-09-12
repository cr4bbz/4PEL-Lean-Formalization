import PEL4.EpistemicHysteresis

namespace PEL4

/-!
# Gate 39: epistemic state sufficiency

Gate 33 established genuine history-sensitive Recovery behavior: the same two
syntactic evidence ingredients can yield different endpoints when an earlier
update changes the extension of later belief-dependent evidence.

Gate 39 asks whether this requires a hidden history register in addition to the
current epistemic model. For Conditionalization the answer is no. Once the
current `Model` is fixed, an identical future evidence schedule determines an
identical future model. Different histories matter only insofar as they leave
different present states.
-/

/-- An arbitrary finite Conditionalization execution. Unlike Gate 38's static
schedule runs, evidence may contain belief operators. Each constructor stores
the admissibility proof needed at the current model. -/
inductive ConditionalizationScheduleRun
    {W Ag Atom : Type} [DecidableEq W] :
    Model W Ag Atom → List (Formula Atom Ag) → Model W Ag Atom → Prop where
  | nil (m : Model W Ag Atom) : ConditionalizationScheduleRun m [] m
  | cons {m out : Model W Ag Atom}
      {E : Formula Atom Ag} {rest : List (Formula Atom Ag)}
      (hAdm : ConditionalizationAdmissible m E)
      (tail : ConditionalizationScheduleRun (conditionalize m E hAdm) rest out) :
      ConditionalizationScheduleRun m (E :: rest) out

/-- A fixed present model and fixed future evidence schedule have a unique
endpoint. Admissibility proofs cannot encode hidden history because they live in
`Prop` and are proof-irrelevant. -/
theorem conditionalizationScheduleRun_deterministic
    {W Ag Atom : Type} [DecidableEq W]
    {m out₁ out₂ : Model W Ag Atom}
    {schedule : List (Formula Atom Ag)}
    (run₁ : ConditionalizationScheduleRun m schedule out₁)
    (run₂ : ConditionalizationScheduleRun m schedule out₂) :
    out₁ = out₂ := by
  induction run₁ with
  | nil m =>
      cases run₂
      rfl
  | @cons m out₁ E rest hAdm₁ tail₁ ih =>
      cases run₂ with
      | cons hAdm₂ tail₂ =>
          have hAdmEq : hAdm₁ = hAdm₂ := Subsingleton.elim _ _
          subst hAdmEq
          exact ih tail₂

/-- Markov/state-sufficiency form: if two histories have merged into the exact
same present model, the same future schedule produces the same endpoint. -/
theorem same_present_same_future
    {W Ag Atom : Type} [DecidableEq W]
    {m n outM outN : Model W Ag Atom}
    {schedule : List (Formula Atom Ag)}
    (hPresent : m = n)
    (runM : ConditionalizationScheduleRun m schedule outM)
    (runN : ConditionalizationScheduleRun n schedule outN) :
    outM = outN := by
  subst n
  exact conditionalizationScheduleRun_deterministic runM runN

/-- Two possibly different finite histories are said to merge when their
endpoints are the same full epistemic model. -/
def EpistemicHistoriesMergeAt
    {W Ag Atom : Type} [DecidableEq W]
    {start₁ start₂ mid₁ mid₂ : Model W Ag Atom}
    {past₁ past₂ : List (Formula Atom Ag)}
    (history₁ : ConditionalizationScheduleRun start₁ past₁ mid₁)
    (history₂ : ConditionalizationScheduleRun start₂ past₂ mid₂) : Prop :=
  mid₁ = mid₂

/-- Once distinct histories merge, every common admissible future coalesces
exactly, including belief-dependent future evidence. -/
theorem merged_histories_common_future_coalesces
    {W Ag Atom : Type} [DecidableEq W]
    {start₁ start₂ mid₁ mid₂ out₁ out₂ : Model W Ag Atom}
    {past₁ past₂ future : List (Formula Atom Ag)}
    (history₁ : ConditionalizationScheduleRun start₁ past₁ mid₁)
    (history₂ : ConditionalizationScheduleRun start₂ past₂ mid₂)
    (hMerge : EpistemicHistoriesMergeAt history₁ history₂)
    (future₁ : ConditionalizationScheduleRun mid₁ future out₁)
    (future₂ : ConditionalizationScheduleRun mid₂ future out₂) :
    out₁ = out₂ := by
  exact same_present_same_future hMerge future₁ future₂

/-- Exact endpoint equality immediately implies agreement on every modal
observation. -/
theorem same_present_same_future_modal_value
    {W Ag Atom : Type} [DecidableEq W]
    {m n outM outN : Model W Ag Atom}
    {schedule : List (Formula Atom Ag)}
    (hPresent : m = n)
    (runM : ConditionalizationScheduleRun m schedule outM)
    (runN : ConditionalizationScheduleRun n schedule outN)
    (phi : ModalFormula Atom Ag) (w : W) :
    evalModal outM w phi = evalModal outN w phi := by
  rw [same_present_same_future hPresent runM runN]

/-- Exact endpoint equality also forces agreement on compositional Recovery. -/
theorem same_present_same_future_recovery
    {W Ag Atom : Type} [DecidableEq W]
    {m n outM outN : Model W Ag Atom}
    {schedule : List (Formula Atom Ag)}
    (hPresent : m = n)
    (runM : ConditionalizationScheduleRun m schedule outM)
    (runN : ConditionalizationScheduleRun n schedule outN)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecovery outM phi ↔
      ModalFormula.CompositionalRecovery outN phi := by
  rw [same_present_same_future hPresent runM runN]

/-! ## Gate-33 diagnostic: history has already changed the present -/

/-- Belief-first in Gate 33 leaves `B p` true at the problematic world `b`.
The first belief-evidence event is the full state space and is informationally
inert there. -/
theorem gate39_gate33_belFirst_belP_at_b :
    evalModal Gate33BelFirst DynamicInstabilityWorld.b dynamicInstabilityBelP =
      FDEValue.T := by
  decide +kernel

/-- Atomic `e` first produces the familiar belief gap `N` at world `b`. -/
theorem gate39_gate33_eFirst_belP_at_b :
    evalModal Gate33EFirst DynamicInstabilityWorld.b dynamicInstabilityBelP =
      FDEValue.N := by
  decide +kernel

/-- The two Gate-33 histories have not secretly reached the same present state:
their intermediate full models are genuinely different. -/
theorem gate39_gate33_intermediate_states_differ :
    Gate33BelFirst ≠ Gate33EFirst := by
  intro hEq
  have hEval := congrArg
    (fun model =>
      evalModal model DynamicInstabilityWorld.b dynamicInstabilityBelP) hEq
  rw [gate39_gate33_belFirst_belP_at_b,
      gate39_gate33_eFirst_belP_at_b] at hEval
  have hPos : true = false := congrArg (fun v : FDEValue => v.pos) hEval
  decide at hPos

/-!
## Gate-39 conclusion

Conditionalization is history-sensitive but state-sufficient:

```text
different history -> different present model -> different future may follow
same present model + same future schedule -> exactly same future model
```

Thus Gate-33 hysteresis does not require an extra memory variable. The current
4PEL model is already a sufficient statistic for all future Conditionalization
dynamics represented by this update rule.

This result is stronger than a Recovery-level Markov claim: endpoint `Model`
equality itself is deterministic, so every modal value and every derived
Recovery judgment coincide.
-/

end PEL4
