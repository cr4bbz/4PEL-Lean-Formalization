import PEL4.KnowledgeSanity

namespace PEL4

/-!
# Knowledge conjunction transport boundary

The knowledge sanity gate establishes that positive evidence-stable knowledge
is not closed under conjunction elimination in general. This module isolates
the exact missing condition.

If `K+(phi and psi)` holds, then both conjuncts already have universal positive
support throughout the accessible range. Therefore the only remaining
requirement for `K+(phi)` is stability of the complete FDE value of `phi`, and
symmetrically for `psi`.

So conjunction elimination does not fail by losing positive support. It fails
when a stable conjunction masks instability in one of its components.
-/

/-- Positive knowledge of a conjunction always gives the ordinary universal
positive-support condition for the left conjunct. -/
theorem positive_conjunction_knowledge_implies_left_box
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hK : evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true) :
    standardBoxPositive m i w phi = true := by
  have hbox := evidence_stable_knowledge_implies_standard_box
    m i w (Formula.and phi psi) hK
  simp only [standardBoxPositive, List.all_eq_true] at hbox ⊢
  intro w' hw'
  have hpair := hbox w' hw'
  change ((eval m w' phi).pos && (eval m w' psi).pos) = true at hpair
  cases hp : (eval m w' phi).pos <;> simp_all

/-- Positive knowledge of a conjunction always gives the ordinary universal
positive-support condition for the right conjunct. -/
theorem positive_conjunction_knowledge_implies_right_box
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hK : evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true) :
    standardBoxPositive m i w psi = true := by
  have hbox := evidence_stable_knowledge_implies_standard_box
    m i w (Formula.and phi psi) hK
  simp only [standardBoxPositive, List.all_eq_true] at hbox ⊢
  intro w' hw'
  have hpair := hbox w' hw'
  change ((eval m w' phi).pos && (eval m w' psi).pos) = true at hpair
  cases hq : (eval m w' psi).pos <;> simp_all

/-- Left Stability Boundary Theorem.

Once positive knowledge of the conjunction is given, positive knowledge of the
left conjunct holds exactly when that conjunct has a stable complete FDE value
over the accessible range. -/
theorem positive_conjunction_elimination_left_iff_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hK : evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true) :
    evidenceStableKnowledgePositive m i w phi = true ↔
      accessibleFDEValueStable m i w phi = true := by
  have hbox := positive_conjunction_knowledge_implies_left_box
    m i w phi psi hK
  simp [evidenceStableKnowledgePositive, hbox]

/-- Right Stability Boundary Theorem. -/
theorem positive_conjunction_elimination_right_iff_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hK : evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true) :
    evidenceStableKnowledgePositive m i w psi = true ↔
      accessibleFDEValueStable m i w psi = true := by
  have hbox := positive_conjunction_knowledge_implies_right_box
    m i w phi psi hK
  simp [evidenceStableKnowledgePositive, hbox]

/-- Conjunction elimination is recovered on the left whenever the left
conjunct's FDE status is stable. -/
theorem positive_conjunction_elimination_left_of_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hK : evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true)
    (hstable : accessibleFDEValueStable m i w phi = true) :
    evidenceStableKnowledgePositive m i w phi = true := by
  exact (positive_conjunction_elimination_left_iff_stable
    m i w phi psi hK).2 hstable

/-- Conjunction elimination is recovered on the right whenever the right
conjunct's FDE status is stable. -/
theorem positive_conjunction_elimination_right_of_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hK : evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true)
    (hstable : accessibleFDEValueStable m i w psi = true) :
    evidenceStableKnowledgePositive m i w psi = true := by
  exact (positive_conjunction_elimination_right_iff_stable
    m i w phi psi hK).2 hstable

/-- The existing crossed T/B countermodel sits exactly on the failure side of
the boundary: the conjunction is stable while both components are unstable. -/
theorem conjunction_countermodel_masks_component_instability :
    accessibleFDEValueStable KnowledgeConjModel KnowledgeConjAgent.a
        KnowledgeConjWorld.root knowledgeConjPQ = true ∧
    accessibleFDEValueStable KnowledgeConjModel KnowledgeConjAgent.a
        KnowledgeConjWorld.root knowledgeConjP = false ∧
    accessibleFDEValueStable KnowledgeConjModel KnowledgeConjAgent.a
        KnowledgeConjWorld.root knowledgeConjQ = false := by
  native_decide

/-!
## Interpretation

For evidence-stable four-valued knowledge, positive conjunction elimination has
an exact local boundary:

  K+(phi and psi) plus Stable(phi)  iff  K+(phi),
  K+(phi and psi) plus Stable(psi)  iff  K+(psi).

The conjunction premise already transports positive support to each component.
What it does not transport is component-level information stability. Hence the
structural failure is not ordinary truth-functional conjunction elimination;
it is a failure of stability reflection from a composite representation to its
parts.

This gives a sharper target for Fitch. Any Fitch-style derivation that extracts
`K(phi)` from `K(phi and psi)` must either assume this stability condition,
operate in a fragment where it is guaranteed, or use a stronger knowledge
semantics that validates the transport globally.
-/

end PEL4
