import PEL4.EpistemicHysteresis

namespace PEL4

/-!
# Gate 36: semantic feedback boundary

Gate 33 showed that the same syntactic evidence formula can denote a different
positive conditioning event after an earlier update. The witness used belief
evidence `B p`. Gate 36 isolates a guaranteed static fragment.

For the evidence language `Formula`, every formula containing no `bel` node is
invariant under probability-only conditionalization. Consequently its positive
evidence extension is invariant as well. A belief node is therefore necessary
for this particular semantic-feedback mechanism, though its mere presence is
not claimed to be sufficient for update sensitivity.
-/

/-- Syntactic fragment of evidence formulas whose evaluation cannot inspect the
probability measure. -/
def Formula.BeliefFree {Atom Ag : Type} : Formula Atom Ag → Prop
  | .prop _ => True
  | .not phi => phi.BeliefFree
  | .and phi psi => phi.BeliefFree ∧ psi.BeliefFree
  | .bel _ _ => False

/-- Probability-only conditionalization preserves the complete FDE value of
belief-free evidence formulas at every world. -/
theorem eval_conditionalize_eq_of_beliefFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update)
    (phi : Formula Atom Ag)
    (hFree : phi.BeliefFree) :
    ∀ w, eval (conditionalize m update hAdm) w phi = eval m w phi := by
  induction phi with
  | prop p =>
      intro w
      rfl
  | not phi ih =>
      intro w
      simp only [Formula.BeliefFree] at hFree
      change FDEValue.not (eval (conditionalize m update hAdm) w phi) =
        FDEValue.not (eval m w phi)
      rw [ih hFree w]
  | and phi psi ihPhi ihPsi =>
      intro w
      simp only [Formula.BeliefFree] at hFree
      change FDEValue.and
          (eval (conditionalize m update hAdm) w phi)
          (eval (conditionalize m update hAdm) w psi) =
        FDEValue.and (eval m w phi) (eval m w psi)
      rw [ihPhi hFree.1 w, ihPsi hFree.2 w]
  | bel i phi ih =>
      simp only [Formula.BeliefFree] at hFree

/-- The positive conditioning event denoted by `evidence` is unchanged by an
update. Exact list equality is used here because conditionalization preserves
accessibility and belief-free evaluation pointwise. -/
def EvidenceExtensionStableUnder
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update evidence : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update) : Prop :=
  ∀ (i : Ag) (w : W),
    conditionalizationEvidenceEvent (conditionalize m update hAdm) i w evidence =
      conditionalizationEvidenceEvent m i w evidence

/-- Complementary witness predicate: at some local coordinate, the same
syntactic evidence formula denotes a different positive event after updating. -/
def EvidenceExtensionSensitiveUnder
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update evidence : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update) : Prop :=
  ∃ (i : Ag) (w : W),
    conditionalizationEvidenceEvent (conditionalize m update hAdm) i w evidence ≠
      conditionalizationEvidenceEvent m i w evidence

/-- Belief-free evidence is extension-stable under every admissible
conditionalization. This is the static side of the Gate-33 boundary. -/
theorem beliefFree_evidenceExtensionStableUnder
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update evidence : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update)
    (hFree : evidence.BeliefFree) :
    EvidenceExtensionStableUnder m update evidence hAdm := by
  intro i w
  unfold conditionalizationEvidenceEvent
  change filterWorlds (m.R i w)
      (fun u => (eval (conditionalize m update hAdm) u evidence).pos) =
    filterWorlds (m.R i w) (fun u => (eval m u evidence).pos)
  have hEval :
      (fun u => (eval (conditionalize m update hAdm) u evidence).pos) =
        (fun u => (eval m u evidence).pos) := by
    funext u
    rw [eval_conditionalize_eq_of_beliefFree m update hAdm evidence hFree u]
  rw [hEval]

/-- Atomic evidence is always in the guaranteed extension-stable fragment. -/
theorem atomic_evidenceExtensionStableUnder
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update)
    (p : Atom) :
    EvidenceExtensionStableUnder m update (Formula.prop p) hAdm := by
  exact beliefFree_evidenceExtensionStableUnder
    m update (Formula.prop p) hAdm (by trivial)

/-- Extension stability and extension sensitivity are mutually exclusive. -/
theorem evidenceExtensionStable_not_sensitive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update evidence : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update)
    (hStable : EvidenceExtensionStableUnder m update evidence hAdm) :
    ¬ EvidenceExtensionSensitiveUnder m update evidence hAdm := by
  intro hSensitive
  rcases hSensitive with ⟨i, w, hNe⟩
  exact hNe (hStable i w)

/-- Gate 33 lies outside the guaranteed static fragment: its belief evidence is
syntactically not belief-free. -/
theorem gate36_gate33_belP_not_beliefFree :
    ¬ gate33BelPEvidence.BeliefFree := by
  simp [gate33BelPEvidence, Formula.BeliefFree]

/-- The Gate-33 witness is genuinely semantically feedback-sensitive under the
atomic `e` update. -/
theorem gate36_gate33_belP_extension_sensitive :
    EvidenceExtensionSensitiveUnder
      DynamicInstabilityModel dynamicInstabilityEvidence gate33BelPEvidence
      dynamic_instability_evidence_admissible := by
  refine ⟨DynamicInstabilityAgent.i, DynamicInstabilityWorld.a, ?_⟩
  intro hEq
  exact gate33_belP_evidence_extension_changes hEq.symm

/-- No belief-free evidence formula can realize the Gate-33 extension-change
mechanism under an admissible conditionalization. -/
theorem gate36_no_beliefFree_extension_feedback
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (update evidence : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m update)
    (hFree : evidence.BeliefFree) :
    ¬ EvidenceExtensionSensitiveUnder m update evidence hAdm := by
  exact evidenceExtensionStable_not_sensitive m update evidence hAdm
    (beliefFree_evidenceExtensionStableUnder m update evidence hAdm hFree)

/-!
## Gate-36 boundary

Verified safe direction:

```text
belief-free evidence
  => evaluation invariant under conditionalization
  => positive evidence extension invariant
  => Gate-33 semantic-feedback mechanism impossible.
```

Verified counter-side:

```text
belief evidence can be extension-sensitive.
```

The converse is intentionally not asserted. A formula may contain `bel` and
still happen to be extension-stable in a particular model or under a particular
update. Gate 36 identifies a sufficient static fragment and a concrete dynamic
boundary, not a syntactic iff-characterization of all feedback-sensitive
formulas.
-/

end PEL4
