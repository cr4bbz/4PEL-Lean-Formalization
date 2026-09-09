import PEL4.LockeanThresholdPhaseTransition

namespace PEL4

/-!
# Gate 7: formula recovery under probability integrity

Gate 6 required full `BeliefThresholdRegular` at every belief node: threshold
completeness plus threshold consistency. Gate 7 proves that the consistency half
is automatic whenever the local probability model satisfies
`ModelProbabilityIntegrity` and the accessible subformula profile is classical.

This file therefore defines a strictly sharper recursive recovery contract for
integrity-certified models. At a belief node the only extra threshold obligation
is decisiveness/completeness. Glut-freedom is derived from the probability laws
and the built-in supermajority threshold.
-/

/-- Recursive classical-recovery admissibility specialized to models carrying
finite probability integrity. A belief node asks only for classical recovery of
the subformula throughout the accessible range and for threshold completeness. -/
def Formula.ProbabilityRecoveryAdmissibleAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : W → Formula Atom Ag → Prop
  | w, Formula.prop p => IsClassicalValue (m.val w p)
  | w, Formula.not phi => Formula.ProbabilityRecoveryAdmissibleAt m w phi
  | w, Formula.and phi psi =>
      Formula.ProbabilityRecoveryAdmissibleAt m w phi ∧
      Formula.ProbabilityRecoveryAdmissibleAt m w psi
  | w, Formula.bel i phi =>
      (∀ u, u ∈ m.R i w → Formula.ProbabilityRecoveryAdmissibleAt m u phi) ∧
      BeliefThresholdComplete m i w (fun u => eval m u phi)

/-- Under probability integrity, the reduced admissibility predicate suffices to
recover a classical value for every legacy formula. In particular, no separate
threshold-consistency premise appears at belief nodes. -/
theorem eval_isClassical_of_probabilityRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag) :
    ∀ w,
      Formula.ProbabilityRecoveryAdmissibleAt m w phi →
      IsClassicalValue (eval m w phi) := by
  induction phi with
  | prop p =>
      intro w h
      exact h
  | not phi ih =>
      intro w h
      exact classicalValue_not _ (ih w h)
  | and phi psi ihPhi ihPsi =>
      intro w h
      exact classicalValue_and _ _ (ihPhi w h.1) (ihPsi w h.2)
  | bel i phi ih =>
      intro w h
      have hClassical :
          ∀ u, u ∈ m.R i w → IsClassicalValue (eval m u phi) := by
        intro u hu
        exact ih u (h.1 u hu)
      exact
        (probabilityIntegrity_classicalProfile_beliefClassical_iff_complete
          m hIntegrity i w (fun u => eval m u phi) hClassical).2 h.2

/-- Global probability-integrity recovery contract. -/
def Formula.ProbabilityRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : Formula Atom Ag) : Prop :=
  ∀ w, Formula.ProbabilityRecoveryAdmissibleAt m w phi

/-- Globally probability-recovery-admissible formulas evaluate classically at
every world of an integrity-certified model. -/
theorem eval_isClassical_of_global_probabilityRecoveryAdmissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag)
    (h : Formula.ProbabilityRecoveryAdmissible m phi) :
    ∀ w, IsClassicalValue (eval m w phi) := by
  intro w
  exact eval_isClassical_of_probabilityRecoveryAdmissible
    m hIntegrity phi w (h w)

/-- On an integrity-certified classical accessible profile, nonclassical belief
is exactly threshold incompleteness. The contradiction/glut branch has vanished. -/
theorem probabilityIntegrity_classicalProfile_beliefNonclassical_iff_incomplete
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ m.R i w → IsClassicalValue (value u)) :
    (¬ IsClassicalValue (belief m i w value)) ↔
      ¬ BeliefThresholdComplete m i w value := by
  have hExact := probabilityIntegrity_classicalProfile_beliefClassical_iff_complete
    m hIntegrity i w value hClassical
  constructor
  · intro hNonclassical hComplete
    exact hNonclassical (hExact.2 hComplete)
  · intro hIncomplete hClassicalBelief
    exact hIncomplete (hExact.1 hClassicalBelief)

end PEL4
