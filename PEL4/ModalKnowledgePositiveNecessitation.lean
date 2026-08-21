import PEL4.ModalKnowledgeNecessitationBoundary

namespace PEL4

/-!
# Exact positive necessitation boundary

The preceding necessitation gate established two facts:

* strict validity is preserved by `K` once the explicitly listed world set is
  closed under accessibility;
* positive/designated validity can still fail to be preserved in an
  accessibility-closed model because complete FDE values may vary between
  positively designated values such as `T` and `B`.

This module isolates the exact missing condition.  Once accessibility closure
ensures that every epistemically inspected world is covered by positive
validity, positive knowledge at a listed world requires exactly one further
ingredient: stability of the complete FDE profile over that world's accessible
range.
-/

/-- A formula has a stable accessible FDE profile at every explicitly listed
world for one agent. -/
def ModalAccessibleValueStableInForAgent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, w ∈ m.worlds →
    modalAccessibleValueStable (m.R i w)
      (fun u => evalModal m u phi) = true

/-- Under accessibility closure and positive validity of `phi`, positive
validity of `K phi` is equivalent to accessible full-value stability at every
listed world. -/
theorem modal_positive_necessitation_iff_accessible_stability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (phi : ModalFormula Atom Ag)
    (hClosed : ModalAccessibilityClosedForAgent m i)
    (hValid : modalPositiveValidIn m phi) :
    modalPositiveValidIn m (ModalFormula.know i phi) ↔
      ModalAccessibleValueStableInForAgent m i phi := by
  constructor
  · intro hKValid
    intro w hw
    have hKAt := hKValid w hw
    unfold modalPositiveAt at hKAt
    have hKnown : modalPositiveKnownAt m i w phi := by
      unfold modalPositiveKnownAt
      exact hKAt
    exact modal_positive_known_implies_stable m i w phi hKnown
  · intro hStable
    unfold modalPositiveValidIn
    intro w hw
    unfold modalPositiveAt
    have hAllPos :
        (m.R i w).all (fun u => (evalModal m u phi).pos) = true := by
      simp only [List.all_eq_true]
      intro u hu
      have huWorld : u ∈ m.worlds := hClosed w hw u hu
      have hPos := hValid u huWorld
      unfold modalPositiveAt at hPos
      exact hPos
    have hStableAt := hStable w hw
    change
      ((m.R i w).all (fun u => (evalModal m u phi).pos) &&
        modalAccessibleValueStable (m.R i w)
          (fun u => evalModal m u phi)) = true
    simp [hAllPos, hStableAt]

/-- Formula-level positive necessitation recovery: closure plus positive
validity plus accessible full-value stability yields positive knowledge-validity. -/
theorem modal_positive_necessitation_of_accessibility_closed_and_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (phi : ModalFormula Atom Ag)
    (hClosed : ModalAccessibilityClosedForAgent m i)
    (hValid : modalPositiveValidIn m phi)
    (hStable : ModalAccessibleValueStableInForAgent m i phi) :
    modalPositiveValidIn m (ModalFormula.know i phi) := by
  exact (modal_positive_necessitation_iff_accessible_stability
    m i phi hClosed hValid).2 hStable

/-- Every positively valid formula is accessibility-stable for one agent.  This
is the exact model-level information condition needed for positive
necessitation once domain closure is available. -/
def ModalPositiveValidityStableForAgent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ phi : ModalFormula Atom Ag,
    modalPositiveValidIn m phi →
    ModalAccessibleValueStableInForAgent m i phi

/-- Under accessibility closure, the positive necessitation schema is equivalent
to stability of every positively valid formula over every accessible range. -/
theorem modal_positive_necessitation_schema_iff_validity_stability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hClosed : ModalAccessibilityClosedForAgent m i) :
    ModalPositiveKnowledgeNecessitationIn m i ↔
      ModalPositiveValidityStableForAgent m i := by
  constructor
  · intro hNec phi hValid
    have hKValid := hNec phi hValid
    exact (modal_positive_necessitation_iff_accessible_stability
      m i phi hClosed hValid).1 hKValid
  · intro hStable phi hValid
    exact (modal_positive_necessitation_iff_accessible_stability
      m i phi hClosed hValid).2 (hStable phi hValid)

/-- The existing `T/B` gate fails precisely the model-level stability condition
for positive necessitation. -/
theorem knowledge_gate_positive_validity_stability_fails :
    ¬ ModalPositiveValidityStableForAgent
      KnowledgeGateModel KnowledgeGateAgent.a := by
  intro hStableSchema
  have hStableAll := hStableSchema modalGateP knowledge_gate_p_positive_valid
  have hStableRoot := hStableAll KnowledgeGateWorld.root (by native_decide)
  have hUnstableRoot :
      modalAccessibleValueStable
          (KnowledgeGateModel.R KnowledgeGateAgent.a KnowledgeGateWorld.root)
          (fun u => evalModal KnowledgeGateModel u modalGateP) = false :=
    modal_positive_belief_upgrade_failure_is_instability.2.1
  rw [hUnstableRoot] at hStableRoot
  exact (by native_decide : false ≠ true) hStableRoot

/-!
## Interpretation

Positive necessitation now has an exact decomposition.

At the formula level, under accessibility closure and positive validity:

```text
positive K-validity
iff
accessible full-value stability at every listed world.
```

At the model-schema level, under accessibility closure:

```text
positive necessitation
iff
every positively valid formula is accessibility-stable.
```

So the classical necessitation rule splits into two independent transports:

1. domain coverage: accessibility must not escape the validity domain;
2. information invariance: positive truth must not vary among different complete
   FDE statuses across an epistemic range.

Strict `T` validity supplies the second condition automatically because every
covered accessible value is exactly `T`.  Positive/designated validity does not,
which is why the `T/B` gate is the canonical failure witness.
-/

end PEL4
