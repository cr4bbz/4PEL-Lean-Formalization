import PEL4.Syntax

namespace PEL4

/-- ST-Validity semantic entailment (Strict-Tolerant):
    If `phi` is strictly true (pos = true, neg = false), `psi` must be tolerantly true (pos = true).
-/
def ST_SemanticEntails {Atom Ag : Type} (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    (eval m w phi) = { pos := true, neg := false } → (eval m w psi).pos = true

/-- LP-Validity semantic entailment (Tolerant-Tolerant):
    If `phi` is tolerantly true (pos = true), `psi` must be tolerantly true.
-/
def LP_SemanticEntails {Atom Ag : Type} (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    (eval m w phi).pos = true → (eval m w psi).pos = true

/-- The Soundness Theorem:
    If `phi` ST-entails `psi` in our calculus, then it is semantically ST-valid. -/
theorem soundness {Atom Ag : Type} (phi psi : Formula Atom Ag) (d : ST_Entails phi psi) : 
  ST_SemanticEntails phi psi := by
  induction d
  case id phi => 
    intro W _ m w h_strict
    exact congrArg FDEValue.pos h_strict
  case double_neg_elim phi =>
    intro W _ m w h_strict
    exact congrArg FDEValue.pos h_strict
  case double_neg_intro phi =>
    intro W _ m w h_strict
    exact congrArg FDEValue.pos h_strict
  case and_elim_l phi psi =>
    intro W _ m w h_strict
    have h1 : ((eval m w phi).pos && (eval m w psi).pos) = true := congrArg FDEValue.pos h_strict
    simp at h1
    exact h1.1
  case and_elim_r phi psi =>
    intro W _ m w h_strict
    have h1 : ((eval m w phi).pos && (eval m w psi).pos) = true := congrArg FDEValue.pos h_strict
    simp at h1
    exact h1.2
  case or_intro_l phi psi =>
    intro W _ m w h_strict
    have h_pos : (eval m w phi).pos = true := congrArg FDEValue.pos h_strict
    simp [Formula.or, eval, FDEValue.not, FDEValue.and, h_pos]
  case or_intro_r phi psi =>
    intro W _ m w h_strict
    have h_pos : (eval m w psi).pos = true := congrArg FDEValue.pos h_strict
    simp [Formula.or, eval, FDEValue.not, FDEValue.and, h_pos]
  case de_morgan phi psi =>
    intro W _ m w h_strict
    exact congrArg FDEValue.pos h_strict
  case mp phi psi =>
    intro W _ m w h_strict
    have h1 : ((eval m w phi).pos && (eval m w (Formula.implies phi psi)).pos) = true := congrArg FDEValue.pos h_strict
    have h2 : ((eval m w phi).neg || (eval m w (Formula.implies phi psi)).neg) = false := congrArg FDEValue.neg h_strict
    simp at h1
    simp at h2
    have h1_neg : (eval m w phi).neg = false := h2.1
    have h2_pos : (eval m w (Formula.implies phi psi)).pos = true := h1.2
    have h3 : (eval m w (Formula.implies phi psi)).pos = ((eval m w phi).neg || (eval m w psi).pos) := rfl
    rw [h3, h1_neg] at h2_pos
    exact h2_pos

end PEL4
