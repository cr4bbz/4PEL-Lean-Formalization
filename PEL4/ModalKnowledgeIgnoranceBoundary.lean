import PEL4.ModalKnowledgeNegativeIntrospection

namespace PEL4

/-!
# Meta-level ignorance versus internal negative knowledge

The preceding modal-law gates recover strong introspection principles for the
primitive evidence-stable knowledge operator.  A remaining distinction is not
primarily about frame structure at all:

* `modalLacksPositiveKnowledgeAt` is a meta-level statement that the positive
  component of `K phi` is false;
* positive support for internal `not K phi` is the negative component of the
  object-language value `K phi`.

These coincide only when the gap value `N` is excluded at the relevant
knowledge claim.  This module isolates that boundary independently of the
Church--Fitch application.
-/

/-- Local bridge from meta-level lack of positive knowledge to negative support
for the object-language knowledge claim.  This is the general modal form of the
NoGap bridge used in the Church--Fitch development. -/
def ModalMetaIgnoranceNoGapAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  modalLacksPositiveKnowledgeAt m i w phi →
    modalNegativeKnowledgeAt m i w phi

/-- Under transitivity and Euclideanness, the NoGap bridge converts meta-level
ignorance into positive knowledge of internal ignorance. -/
theorem modal_meta_ignorance_recovers_internal_negative_introspection
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hEuclid : ModalEuclideanAt m i w)
    (hNoGap : ModalMetaIgnoranceNoGapAt m i w phi)
    (hLacks : modalLacksPositiveKnowledgeAt m i w phi) :
    modalPositiveKnownAt m i w
      (ModalFormula.not (ModalFormula.know i phi)) := by
  unfold ModalMetaIgnoranceNoGapAt at hNoGap
  unfold modalPositiveKnownAt
  exact modal_positive_internal_negative_introspection_of_transitive_euclidean
    m i w phi hTrans hEuclid (hNoGap hLacks)

/-!
## A one-world S5-like gap witness

The single world is reflexive and its accessibility relation is trivially
transitive and Euclidean.  The atom `p` has value `N`.  Because the singleton
accessible profile is stably `N`, evidence-stable knowledge also has value `N`:

  K p = N.

Therefore positive knowledge is absent, but internal `not K p` is also `N`, not
positively supported.  Knowledge of that internal ignorance remains `N`.

Thus even the strongest familiar local frame geometry cannot turn meta-level
lack of positive knowledge into internal negative evidence.  The missing bridge
is semantic NoGap, not another accessibility condition.
-/

inductive IgnoranceAtom where
  | p
deriving DecidableEq, Repr

inductive IgnoranceAgent where
  | a
deriving DecidableEq, Repr

inductive IgnoranceWorld where
  | w
deriving DecidableEq, Repr

def ignoranceR :
    IgnoranceAgent → IgnoranceWorld → FiniteSet IgnoranceWorld
  | _, _ => [IgnoranceWorld.w]

def ignoranceVal : IgnoranceWorld → IgnoranceAtom → FDEValue
  | _, _ => FDEValue.N

def ignoranceMu : IgnoranceWorld → FiniteSet IgnoranceWorld → Rat
  | _, S => if S.contains IgnoranceWorld.w then 1 else 0

def IgnoranceGapModel : Model IgnoranceWorld IgnoranceAgent IgnoranceAtom :=
  { worlds := [IgnoranceWorld.w]
  , R := ignoranceR
  , mu := fun _ world => ignoranceMu world
  , val := ignoranceVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro i world
      cases i
      cases world
      native_decide
  , mu_empty := by
      intro i world
      cases i
      cases world
      native_decide
  , c_gt_half := by
      intro i
      cases i
      native_decide
  , c_le_one := by
      intro i
      cases i
      native_decide
  }

def ignoranceP : ModalFormula IgnoranceAtom IgnoranceAgent :=
  ModalFormula.prop IgnoranceAtom.p

/-- The singleton frame is reflexive. -/
theorem ignorance_gap_frame_reflexive :
    IgnoranceWorld.w ∈
      IgnoranceGapModel.R IgnoranceAgent.a IgnoranceWorld.w := by
  native_decide

/-- The singleton frame is locally transitive. -/
theorem ignorance_gap_frame_transitive :
    ModalTransitiveAt IgnoranceGapModel IgnoranceAgent.a
      IgnoranceWorld.w := by
  intro x hx y hy
  cases x
  cases y
  native_decide

/-- The singleton frame is locally Euclidean. -/
theorem ignorance_gap_frame_euclidean :
    ModalEuclideanAt IgnoranceGapModel IgnoranceAgent.a
      IgnoranceWorld.w := by
  intro x hx y hy
  cases x
  cases y
  native_decide

/-- The atom is gap-valued at the unique world. -/
theorem ignorance_gap_p_is_gap :
    evalModal IgnoranceGapModel IgnoranceWorld.w ignoranceP = FDEValue.N := by
  native_decide

/-- Evidence-stable knowledge preserves the homogeneous singleton gap. -/
theorem ignorance_gap_kp_is_gap :
    evalModal IgnoranceGapModel IgnoranceWorld.w
      (ModalFormula.know IgnoranceAgent.a ignoranceP) = FDEValue.N := by
  native_decide

/-- Meta-level positive knowledge is absent. -/
theorem ignorance_gap_lacks_positive_knowledge :
    modalLacksPositiveKnowledgeAt IgnoranceGapModel IgnoranceAgent.a
      IgnoranceWorld.w ignoranceP := by
  unfold modalLacksPositiveKnowledgeAt
  native_decide

/-- Internal `not K p` is gap-valued rather than positively true. -/
theorem ignorance_gap_internal_not_kp_is_gap :
    evalModal IgnoranceGapModel IgnoranceWorld.w
      (ModalFormula.not (ModalFormula.know IgnoranceAgent.a ignoranceP)) =
      FDEValue.N := by
  native_decide

/-- The agent also does not positively know the internal ignorance claim. -/
theorem ignorance_gap_knows_internal_not_kp_is_gap :
    evalModal IgnoranceGapModel IgnoranceWorld.w
      (ModalFormula.know IgnoranceAgent.a
        (ModalFormula.not (ModalFormula.know IgnoranceAgent.a ignoranceP))) =
      FDEValue.N := by
  native_decide

/-- The local NoGap bridge fails in the singleton gap model. -/
theorem ignorance_gap_violates_meta_ignorance_no_gap :
    ¬ ModalMetaIgnoranceNoGapAt IgnoranceGapModel IgnoranceAgent.a
      IgnoranceWorld.w ignoranceP := by
  intro hNoGap
  have hNeg := hNoGap ignorance_gap_lacks_positive_knowledge
  unfold modalNegativeKnowledgeAt at hNeg
  have hNegFalse :
      (evalModal IgnoranceGapModel IgnoranceWorld.w
        (ModalFormula.know IgnoranceAgent.a ignoranceP)).neg = false := by
    native_decide
  rw [hNegFalse] at hNeg
  cases hNeg

/-- Even on a reflexive, transitive, Euclidean singleton frame, meta-level lack
of positive knowledge does not imply positive internal ignorance. -/
theorem meta_ignorance_not_internal_ignorance_on_s5_like_gap_frame :
    IgnoranceWorld.w ∈
        IgnoranceGapModel.R IgnoranceAgent.a IgnoranceWorld.w ∧
    ModalTransitiveAt IgnoranceGapModel IgnoranceAgent.a IgnoranceWorld.w ∧
    ModalEuclideanAt IgnoranceGapModel IgnoranceAgent.a IgnoranceWorld.w ∧
    modalLacksPositiveKnowledgeAt IgnoranceGapModel IgnoranceAgent.a
      IgnoranceWorld.w ignoranceP ∧
    (evalModal IgnoranceGapModel IgnoranceWorld.w
      (ModalFormula.not (ModalFormula.know IgnoranceAgent.a ignoranceP))).pos = false ∧
    (evalModal IgnoranceGapModel IgnoranceWorld.w
      (ModalFormula.know IgnoranceAgent.a
        (ModalFormula.not (ModalFormula.know IgnoranceAgent.a ignoranceP)))).pos = false := by
  refine ⟨ignorance_gap_frame_reflexive,
    ignorance_gap_frame_transitive,
    ignorance_gap_frame_euclidean,
    ignorance_gap_lacks_positive_knowledge, ?_, ?_⟩
  · native_decide
  · native_decide

/-!
## Interpretation

There are now two independent axes in the introspection story:

1. frame transport controls whether already available epistemic values propagate
   through nested knowledge;
2. the NoGap bridge controls whether meta-level absence of positive knowledge
   counts as negative object-language evidence at all.

Transitivity plus Euclideanness solves the first problem but not the second.
The singleton `N` model is already reflexive, transitive, and Euclidean, yet
meta-level ignorance does not become positive internal ignorance.  Adding the
local NoGap bridge is exactly what allows the previously verified internal
negative-introspection theorem to apply.

This separates a semantic information-status boundary from the usual Kripke
frame conditions rather than hiding both under the single label "axiom 5".
-/

end PEL4
