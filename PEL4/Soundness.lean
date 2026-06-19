import PEL4.Syntax

namespace PEL4

/-- LP-Validity semantic entailment (Logic of Paradox):
    If `phi` is tolerantly true (i.e. pos = true), `psi` must be tolerantly true.
    Note: ST-entailment allows strict premises, but LP-entailment is robust
    and prevents chaining issues like Modus Ponens failure.
-/
def LP_SemanticEntails {Atom Ag : Type} (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    (eval m w phi).pos = true → (eval m w psi).pos = true

/-- The Soundness Theorem:
    If `phi` ST-entails `psi` in our safe Hilbert calculus, then it is semantically LP-valid. -/
theorem soundness {Atom Ag : Type} (phi psi : Formula Atom Ag) (d : ST_Entails phi psi) : 
  LP_SemanticEntails phi psi := by
  intro W _ m w h_pos
  induction d with
  | id phi => exact h_pos
  | double_neg_elim phi =>
    exact h_pos
  | double_neg_intro phi =>
    exact h_pos
  | and_elim_l phi psi =>
    have h : ((eval m w phi).pos && (eval m w psi).pos) = true := h_pos
    exact (Bool.and_eq_true _ _).mp h |>.1
  | and_elim_r phi psi =>
    have h : ((eval m w phi).pos && (eval m w psi).pos) = true := h_pos
    exact (Bool.and_eq_true _ _).mp h |>.2
  | or_intro_l phi psi =>
    simp [Formula.or, eval, FDEValue.not, FDEValue.and, h_pos]
  | or_intro_r phi psi =>
    simp [Formula.or, eval, FDEValue.not, FDEValue.and, h_pos]
  | de_morgan phi psi =>
    -- eval(not (and phi psi)).pos is definitionally phi.neg || psi.neg
    -- eval(or (not phi) (not psi)).pos is also definitionally phi.neg || psi.neg
    exact h_pos

end PEL4
