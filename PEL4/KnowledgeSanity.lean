import PEL4.KnowledgeSemantics
import PEL4.EpistemicStatus

namespace PEL4

/-!
# Knowledge sanity gate

This module tests the evidence-stable four-valued knowledge candidate before it
is promoted to a primitive object-language operator.

The gate isolates three issues that matter directly for Fitch-style reasoning:

* reflexive factivity of positive knowledge;
* internal FDE negation versus meta-level absence of positive knowledge;
* failure of unrestricted conjunction elimination for the non-standard
  evidence-stable knowledge semantics.

The last phenomenon is not treated as an implementation accident. It mirrors
the known non-compositional behaviour of the non-standard Belnap-Dunn knowledge
modality when paradoxical values are present.
-/

/-- Meta-level absence of positive evidence-stable knowledge. -/
def lacksPositiveKnowledge {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  !(evidenceStableKnowledgeValue m i w phi).pos

/-- Positive support of the internal FDE negation of the semantic knowledge
value. This is deliberately kept separate from `lacksPositiveKnowledge`. -/
def internallyNegatedKnowledgePositive {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) : Bool :=
  (FDEValue.not (evidenceStableKnowledgeValue m i w phi)).pos

/-- Internal negation of the knowledge value behaves like absence of positive
knowledge exactly when the knowledge value is classical. -/
theorem internal_negated_knowledge_matches_absence_iff_classical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag) :
    internallyNegatedKnowledgePositive m i w phi =
        lacksPositiveKnowledge m i w phi ↔
      isClassical (evidenceStableKnowledgeValue m i w phi) = true := by
  simpa [internallyNegatedKnowledgePositive, lacksPositiveKnowledge] using
    internal_negation_matches_positive_absence_iff_classical
      (evidenceStableKnowledgeValue m i w phi)

/-- Positive evidence-stable knowledge is factive at any reflexive point: if
the actual world is among its own accessible alternatives, positive knowledge
forces positive support for the proposition at the actual world. -/
theorem positive_knowledge_factive_at_reflexive_point
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (phi : Formula Atom Ag)
    (href : w ∈ m.R i w)
    (hK : evidenceStableKnowledgePositive m i w phi = true) :
    (eval m w phi).pos = true := by
  have hbox := evidence_stable_knowledge_implies_standard_box m i w phi hK
  simp only [standardBoxPositive, List.all_eq_true] at hbox
  exact hbox w href

/-!
## Conjunction countermodel

The two accessible worlds exchange the source of paradoxicality:

  left:   p = T, q = B
  right:  p = B, q = T

Hence `p and q` is `B` at both worlds, so its complete FDE value is stable and
positive throughout the accessible range. By contrast, `p` and `q` separately
vary between `T` and `B`, so evidence-stable knowledge rejects each conjunct.

Thus knowledge of the conjunction need not transport to knowledge of either
conjunct.
-/

inductive KnowledgeConjAtom where
  | p | q
deriving DecidableEq, Repr

inductive KnowledgeConjAgent where
  | a
deriving DecidableEq, Repr

inductive KnowledgeConjWorld where
  | root | left | right
deriving DecidableEq, Repr

/-- Crossed `T/B` valuation producing a stable glut at conjunction level. -/
def knowledgeConjVal : KnowledgeConjWorld → KnowledgeConjAtom → FDEValue
| KnowledgeConjWorld.root, KnowledgeConjAtom.p => FDEValue.T
| KnowledgeConjWorld.root, KnowledgeConjAtom.q => FDEValue.T
| KnowledgeConjWorld.left, KnowledgeConjAtom.p => FDEValue.T
| KnowledgeConjWorld.left, KnowledgeConjAtom.q => FDEValue.B
| KnowledgeConjWorld.right, KnowledgeConjAtom.p => FDEValue.B
| KnowledgeConjWorld.right, KnowledgeConjAtom.q => FDEValue.T

/-- Uniform probability over the two accessible worlds. -/
def knowledgeConjMu : FiniteSet KnowledgeConjWorld → Rat
| S =>
  let pl := if S.contains KnowledgeConjWorld.left then (1 : Rat) / 2 else 0
  let pr := if S.contains KnowledgeConjWorld.right then (1 : Rat) / 2 else 0
  pl + pr

/-- Finite model witnessing non-compositional knowledge at conjunction. -/
def KnowledgeConjModel :
    Model KnowledgeConjWorld KnowledgeConjAgent KnowledgeConjAtom :=
  { worlds := [KnowledgeConjWorld.root,
      KnowledgeConjWorld.left, KnowledgeConjWorld.right]
  , R := fun _ _ => [KnowledgeConjWorld.left, KnowledgeConjWorld.right]
  , mu := fun _ _ => knowledgeConjMu
  , val := knowledgeConjVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro _ _
      native_decide
  , mu_empty := by
      intro _ _
      native_decide
  , c_gt_half := by
      intro _
      native_decide
  , c_le_one := by
      intro _
      native_decide
  }


def knowledgeConjP : Formula KnowledgeConjAtom KnowledgeConjAgent :=
  Formula.prop KnowledgeConjAtom.p

def knowledgeConjQ : Formula KnowledgeConjAtom KnowledgeConjAgent :=
  Formula.prop KnowledgeConjAtom.q

def knowledgeConjPQ : Formula KnowledgeConjAtom KnowledgeConjAgent :=
  Formula.and knowledgeConjP knowledgeConjQ

#eval! evidenceStableKnowledgeValue KnowledgeConjModel KnowledgeConjAgent.a
  KnowledgeConjWorld.root knowledgeConjPQ
#eval! evidenceStableKnowledgeValue KnowledgeConjModel KnowledgeConjAgent.a
  KnowledgeConjWorld.root knowledgeConjP
#eval! evidenceStableKnowledgeValue KnowledgeConjModel KnowledgeConjAgent.a
  KnowledgeConjWorld.root knowledgeConjQ

/-- The conjunction is homogeneously glutty and therefore itself known with
value `B`. -/
theorem conjunction_knowledge_is_glut :
    evidenceStableKnowledgeValue KnowledgeConjModel KnowledgeConjAgent.a
      KnowledgeConjWorld.root knowledgeConjPQ = FDEValue.B := by
  native_decide

/-- The left conjunct is epistemically unstable (`T/B`) and therefore its
knowledge value is `F`. -/
theorem left_conjunct_knowledge_is_false :
    evidenceStableKnowledgeValue KnowledgeConjModel KnowledgeConjAgent.a
      KnowledgeConjWorld.root knowledgeConjP = FDEValue.F := by
  native_decide

/-- The right conjunct is epistemically unstable (`B/T`) and therefore its
knowledge value is `F`. -/
theorem right_conjunct_knowledge_is_false :
    evidenceStableKnowledgeValue KnowledgeConjModel KnowledgeConjAgent.a
      KnowledgeConjWorld.root knowledgeConjQ = FDEValue.F := by
  native_decide

/-- Positive knowledge of a conjunction does not in general transport to
positive knowledge of its conjuncts. -/
theorem positive_knowledge_conjunction_elimination_fails :
    evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
        KnowledgeConjWorld.root knowledgeConjPQ = true ∧
    evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
        KnowledgeConjWorld.root knowledgeConjP = false ∧
    evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
        KnowledgeConjWorld.root knowledgeConjQ = false := by
  native_decide

/-!
## Interpretation

The conjunction countermodel is structurally important for Fitch. The classical
knowability argument normally transports knowledge from `K(p and q)` to `K(p)`
and `K(q)`. Evidence-stable Belnapian knowledge does not validate that transport
without additional restrictions.

The failure is specifically driven by a higher-order effect: the conjunction
can have a stable complete value even when the individual conjunct values are
not stable. In the witness above the location of the glut swaps between `p` and
`q`, while their conjunction remains uniformly `B`.

This does not yet settle Fitch. It identifies a candidate transport principle
whose validity must be made explicit rather than assumed.
-/

end PEL4
