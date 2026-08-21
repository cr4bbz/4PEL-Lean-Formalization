import PEL4.ModalLanguage

namespace PEL4

/-!
# Satisfaction, validity, and epistemic schemas for the modal language

The conservative modal language now contains primitive belief, evidence-stable
knowledge, and raw accessibility possibility.  This module adds the semantic
metalanguage needed to state Church--Fitch style principles without identifying
four-valued positive truth with strict classical truth.

Two truth notions are kept explicit:

* positive/designated truth: the positive FDE component is `true`;
* strict truth: the complete FDE value is exactly `T`.

The first Church--Fitch gate will use positive/designated truth.  Strict-`T`
variants are intentionally left distinct for later comparison.
-/

/-- Positive/designated satisfaction at a world. -/
def modalPositiveAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w phi).pos = true

/-- Strict satisfaction at a world: the complete value is exactly `T`. -/
def modalStrictTrueAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : ModalFormula Atom Ag) : Prop :=
  evalModal m w phi = FDEValue.T

/-- Positive validity over the worlds explicitly carried by a model. -/
def modalPositiveValidIn {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, w ∈ m.worlds → modalPositiveAt m w phi

/-- Strict-`T` validity over the worlds explicitly carried by a model. -/
def modalStrictValidIn {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, w ∈ m.worlds → modalStrictTrueAt m w phi

/-- Positive object-language knowledge at a point. -/
def modalPositiveKnownAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.know i phi)).pos = true

/-- Meta-level absence of positive object-language knowledge. -/
def modalLacksPositiveKnowledgeAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.know i phi)).pos = false

/-- Negative support for the object-language knowledge claim. -/
def modalNegativeKnowledgeAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.know i phi)).neg = true

/-- Positive raw knowability: some accessible point positively supports
`K phi`. -/
def modalPositiveKnowableAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w
    (ModalFormula.poss i (ModalFormula.know i phi))).pos = true

/-- Positive Church--Fitch knowability schema for every formula and every world
explicitly listed in the model. -/
def ModalPositiveKnowabilityPrinciple
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ (w : W) (phi : ModalFormula Atom Ag),
    w ∈ m.worlds →
    modalPositiveAt m w phi →
    modalPositiveKnowableAt m i w phi

/-- Positive omniscience schema: every positively true formula is positively
known at the same point. -/
def ModalPositiveOmniscience
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ (w : W) (phi : ModalFormula Atom Ag),
    w ∈ m.worlds →
    modalPositiveAt m w phi →
    modalPositiveKnownAt m i w phi

/-- Strict truth always gives positive/designated truth. -/
theorem modal_strict_true_implies_positive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) (phi : ModalFormula Atom Ag)
    (h : modalStrictTrueAt m w phi) :
    modalPositiveAt m w phi := by
  unfold modalStrictTrueAt at h
  unfold modalPositiveAt
  rw [h]
  rfl

end PEL4
