import PEL4.ClassicalRecovery
import PEL4.Syntax

namespace PEL4

/-!
# Gate 6: formula-level classical recovery

Gate 5 identified exact value-level conditions for the classical `{T,F}` slice.
This module lifts that result through syntax without silently assuming that every
4-PEL operator preserves classicality.

The first theorem is deliberately restricted to the propositional fragment of the
legacy `Formula` language. Negation and conjunction preserve the recovered slice;
disjunction and implication are macros built from them. The Lockean belief
constructor is excluded from the induction and studied as a boundary case.
-/

/-- The fragment of legacy formulas containing no Lockean belief constructor. -/
inductive Formula.IsPropositional {Atom Ag : Type} : Formula Atom Ag → Prop where
  | prop (p : Atom) : Formula.IsPropositional (Formula.prop p)
  | not {phi : Formula Atom Ag} :
      Formula.IsPropositional phi →
      Formula.IsPropositional (Formula.not phi)
  | and {phi psi : Formula Atom Ag} :
      Formula.IsPropositional phi →
      Formula.IsPropositional psi →
      Formula.IsPropositional (Formula.and phi psi)

/-- All atomic values at one world lie in the recovered classical slice. -/
def AtomicClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W) : Prop :=
  ∀ p, IsClassicalValue (m.val w p)

/-- Every atomic valuation in the model lies in the recovered classical slice. -/
def AtomicClassicalModel
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : Prop :=
  ∀ w p, IsClassicalValue (m.val w p)

/-- Global atomic classicality specializes to any world. -/
theorem atomicClassicalModel_at
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (h : AtomicClassicalModel m)
    (w : W) :
    AtomicClassicalAt m w := by
  intro p
  exact h w p

/-- The propositional fragment is closed under the syntactic OR macro. -/
theorem Formula.IsPropositional.or
    {Atom Ag : Type}
    {phi psi : Formula Atom Ag}
    (hphi : Formula.IsPropositional phi)
    (hpsi : Formula.IsPropositional psi) :
    Formula.IsPropositional (Formula.or phi psi) := by
  unfold Formula.or
  exact Formula.IsPropositional.not
    (Formula.IsPropositional.and
      (Formula.IsPropositional.not hphi)
      (Formula.IsPropositional.not hpsi))

/-- The propositional fragment is closed under material implication. -/
theorem Formula.IsPropositional.implies
    {Atom Ag : Type}
    {phi psi : Formula Atom Ag}
    (hphi : Formula.IsPropositional phi)
    (hpsi : Formula.IsPropositional psi) :
    Formula.IsPropositional (Formula.implies phi psi) := by
  unfold Formula.implies
  exact Formula.IsPropositional.or
    (Formula.IsPropositional.not hphi) hpsi

/-- Evaluation of the De-Morgan OR macro agrees with the primitive FDE OR. -/
theorem eval_formula_or
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi psi : Formula Atom Ag) :
    eval m w (Formula.or phi psi) =
      FDEValue.or (eval m w phi) (eval m w psi) := by
  rfl

/-- Main Gate-6 lift: classical atomic values force every propositional formula
at the same world into the exact `{T,F}` slice. -/
theorem eval_isClassical_of_propositional
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    {phi : Formula Atom Ag}
    (hAtoms : AtomicClassicalAt m w)
    (hphi : Formula.IsPropositional phi) :
    IsClassicalValue (eval m w phi) := by
  induction hphi with
  | prop p =>
      exact hAtoms p
  | not h ih =>
      exact classicalValue_not _ ih
  | and hphi hpsi ihPhi ihPsi =>
      exact classicalValue_and _ _ ihPhi ihPsi

/-- Global regular atomic valuation gives formula-level classicality for every
propositional formula at every world. -/
theorem eval_isClassical_of_atomicClassicalModel
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hModel : AtomicClassicalModel m)
    (w : W)
    {phi : Formula Atom Ag}
    (hphi : Formula.IsPropositional phi) :
    IsClassicalValue (eval m w phi) :=
  eval_isClassical_of_propositional m w
    (atomicClassicalModel_at m hModel w) hphi

/-- Formula-level excluded middle in the legacy syntax. -/
def Formula.excludedMiddle {Atom Ag : Type}
    (phi : Formula Atom Ag) : Formula Atom Ag :=
  Formula.or phi (Formula.not phi)

/-- Formula-level contradiction in the legacy syntax. -/
def Formula.contradiction {Atom Ag : Type}
    (phi : Formula Atom Ag) : Formula Atom Ag :=
  Formula.and phi (Formula.not phi)

/-- On a regular propositional valuation, excluded middle evaluates strictly to T. -/
theorem eval_excludedMiddle_eq_T_of_propositional
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    {phi : Formula Atom Ag}
    (hAtoms : AtomicClassicalAt m w)
    (hphi : Formula.IsPropositional phi) :
    eval m w (Formula.excludedMiddle phi) = FDEValue.T := by
  change excludedMiddleValue (eval m w phi) = FDEValue.T
  exact (excludedMiddle_eq_T_iff_classical (eval m w phi)).2
    (eval_isClassical_of_propositional m w hAtoms hphi)

/-- A propositional contradiction on the recovered classical slice is strictly F. -/
theorem eval_contradiction_eq_F_of_propositional
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    {phi : Formula Atom Ag}
    (hAtoms : AtomicClassicalAt m w)
    (hphi : Formula.IsPropositional phi) :
    eval m w (Formula.contradiction phi) = FDEValue.F := by
  change FDEValue.and (eval m w phi) (FDEValue.not (eval m w phi)) =
    FDEValue.F
  rcases eval_isClassical_of_propositional m w hAtoms hphi with hT | hF
  · rw [hT]
    rfl
  · rw [hF]
    rfl

/-- Formula-level LP explosion is recovered on the regular propositional slice.
This remains a restricted-model theorem, not unrestricted LP entailment in 4-PEL. -/
theorem propositional_contradiction_LP_valid
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    {phi : Formula Atom Ag}
    (hAtoms : AtomicClassicalAt m w)
    (hphi : Formula.IsPropositional phi)
    (q : Formula Atom Ag) :
    LP_valid
      (eval m w (Formula.contradiction phi))
      (eval m w q) := by
  rw [eval_contradiction_eq_F_of_propositional m w hAtoms hphi]
  simp [LP_valid, FDEValue.T, FDEValue.B, FDEValue.F]

/-! ## Belief boundary witness -/

/-- Two classical worlds split positive and negative support evenly. -/
def gate6BeliefBoundaryModel : Model Bool Unit Unit where
  worlds := [false, true]
  R := fun _ _ => [false, true]
  mu := fun _ _ S =>
    if S = [false, true] then 1
    else if S = [false] then 1 / 2
    else if S = [true] then 1 / 2
    else 0
  val := fun w _ => if w then FDEValue.F else FDEValue.T
  c := fun _ => 3 / 5
  mu_total := by
    intro _ _
    decide +kernel
  mu_empty := by
    intro _ _
    decide +kernel
  c_gt_half := by
    intro _
    decide +kernel
  c_le_one := by
    intro _
    decide +kernel

/-- The boundary model is atomically classical at every world. -/
theorem gate6BeliefBoundary_atomicClassical :
    AtomicClassicalModel gate6BeliefBoundaryModel := by
  intro w p
  cases p
  cases w <;>
    simp [gate6BeliefBoundaryModel, IsClassicalValue]

/-- Yet Lockean belief can reopen a gap: at threshold 3/5, a 1/2--1/2 split
makes neither the positive nor negative support event reach the threshold. -/
theorem gate6BeliefBoundary_belief_is_N :
    eval gate6BeliefBoundaryModel false
      (Formula.bel () (Formula.prop ())) = FDEValue.N := by
  decide +kernel

/-- Atomic classicality is therefore insufficient for formula-level classicality
once the belief constructor is admitted. -/
theorem atomicClassical_does_not_force_belief_classical :
    AtomicClassicalModel gate6BeliefBoundaryModel ∧
    ¬ IsClassicalValue
      (eval gate6BeliefBoundaryModel false
        (Formula.bel () (Formula.prop ()))) := by
  constructor
  · exact gate6BeliefBoundary_atomicClassical
  · rw [gate6BeliefBoundary_belief_is_N]
    simp [IsClassicalValue, FDEValue.N, FDEValue.T, FDEValue.F]

end PEL4
