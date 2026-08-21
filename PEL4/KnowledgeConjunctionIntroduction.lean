import PEL4.KnowledgeConjunctionBoundary

namespace PEL4

/-!
# Knowledge conjunction introduction

The conjunction-boundary development shows that positive evidence-stable
knowledge does not support unrestricted conjunction elimination: a stable
conjunction can mask instability in either component.

The reverse direction is different. If both components are positively known,
then each already has universal positive support and a stable complete FDE
value. FDE conjunction preserves both facts: positive support combines by
Boolean conjunction, and applying the deterministic FDE conjunction to two
stable component values yields a stable conjunction value.

Thus positive knowledge is closed under conjunction introduction even though it
is not closed under conjunction elimination.
-/

/-- Universal positive support is closed under conjunction introduction. -/
theorem standard_box_positive_conjunction_intro
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hphi : standardBoxPositive m i w phi = true)
    (hpsi : standardBoxPositive m i w psi = true) :
    standardBoxPositive m i w (Formula.and phi psi) = true := by
  simp only [standardBoxPositive, List.all_eq_true] at hphi hpsi ⊢
  intro w' hw'
  have hp := hphi w' hw'
  have hq := hpsi w' hw'
  change ((eval m w' phi).pos && (eval m w' psi).pos) = true
  simp [hp, hq]

/-- Stability of the complete FDE value is closed under conjunction of two
stable components. -/
theorem conjunction_stable_of_components_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hphi : accessibleFDEValueStable m i w phi = true)
    (hpsi : accessibleFDEValueStable m i w psi = true) :
    accessibleFDEValueStable m i w (Formula.and phi psi) = true := by
  unfold accessibleFDEValueStable at hphi hpsi ⊢
  cases hR : m.R i w with
  | nil =>
      simp [hR]
  | cons first rest =>
      simp only [hR, List.all_eq_true] at hphi hpsi ⊢
      intro w' hw'
      have hphi' := hphi w' hw'
      have hpsi' := hpsi w' hw'
      have hphiEq : eval m w' phi = eval m first phi :=
        of_decide_eq_true hphi'
      have hpsiEq : eval m w' psi = eval m first psi :=
        of_decide_eq_true hpsi'
      simp [hphiEq, hpsiEq]

/-- Positive evidence-stable knowledge is closed under conjunction
introduction. No additional frame or stability assumption is needed beyond the
two knowledge premises themselves. -/
theorem positive_knowledge_conjunction_introduction
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : Formula Atom Ag)
    (hKphi : evidenceStableKnowledgePositive m i w phi = true)
    (hKpsi : evidenceStableKnowledgePositive m i w psi = true) :
    evidenceStableKnowledgePositive m i w (Formula.and phi psi) = true := by
  have hboxPhi := evidence_stable_knowledge_implies_standard_box
    m i w phi hKphi
  have hboxPsi := evidence_stable_knowledge_implies_standard_box
    m i w psi hKpsi
  have hstablePhi : accessibleFDEValueStable m i w phi = true := by
    cases hs : accessibleFDEValueStable m i w phi <;>
      simp_all [evidenceStableKnowledgePositive]
  have hstablePsi : accessibleFDEValueStable m i w psi = true := by
    cases hs : accessibleFDEValueStable m i w psi <;>
      simp_all [evidenceStableKnowledgePositive]
  have hboxAnd := standard_box_positive_conjunction_intro
    m i w phi psi hboxPhi hboxPsi
  have hstableAnd := conjunction_stable_of_components_stable
    m i w phi psi hstablePhi hstablePsi
  simp [evidenceStableKnowledgePositive, hboxAnd, hstableAnd]

/-- The existing crossed T/B model witnesses the directional asymmetry of
knowledge/conjunction transport: introduction is available whenever both
conjuncts are positively known, while elimination fails in this concrete model. -/
theorem conjunction_transport_directional_asymmetry :
    (evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
          KnowledgeConjWorld.root knowledgeConjP = true →
      evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
          KnowledgeConjWorld.root knowledgeConjQ = true →
      evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
          KnowledgeConjWorld.root knowledgeConjPQ = true) ∧
    (evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
          KnowledgeConjWorld.root knowledgeConjPQ = true ∧
      evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
          KnowledgeConjWorld.root knowledgeConjP = false ∧
      evidenceStableKnowledgePositive KnowledgeConjModel KnowledgeConjAgent.a
          KnowledgeConjWorld.root knowledgeConjQ = false) := by
  constructor
  · intro hp hq
    exact positive_knowledge_conjunction_introduction
      KnowledgeConjModel KnowledgeConjAgent.a KnowledgeConjWorld.root
      knowledgeConjP knowledgeConjQ hp hq
  · exact positive_knowledge_conjunction_elimination_fails

/-!
## Interpretation

The two conjunction directions have different structural behaviour:

  K+(phi) and K+(psi)  ->  K+(phi and psi)

holds generally, because stability and positive support compose forward through
FDE conjunction. But

  K+(phi and psi)  ->  K+(phi)

requires component-level stability, as characterized by the boundary theorems.

The asymmetry can therefore be stated as a transport principle:

  composition preserves epistemic stability,
  decomposition need not reflect epistemic stability.

For Fitch-style reasoning this matters because the problematic step is the
eliminative direction: extracting knowledge of a component from knowledge of a
compound. The introduction direction itself is not where the evidence-stable
semantics departs from the classical pattern.
-/

end PEL4
