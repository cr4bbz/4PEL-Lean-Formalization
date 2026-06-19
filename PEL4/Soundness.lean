import PEL4.Syntax

namespace PEL4

/-- ST-Validity semantic entailment:
    If `phi` is strictly true, `psi` must be tolerantly true.
    In FDE terms, `phi` strictly true means `pos = true` and `neg = false`.
    But ST consequence typically just requires: if `v^+(phi) = 1` then `v^+(psi) = 1`.
    Let's define ST-entailment SEMANTICALLY as:
    ∀ m w, (eval m w phi).pos = true → (eval m w psi).pos = true
-/
def ST_SemanticEntails {Atom Ag : Type} (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    (eval m w phi).pos = true → (eval m w psi).pos = true

/-- The Soundness Theorem:
    If `phi` ST-entails `psi` in our Hilbert calculus, then it is semantically ST-valid. -/
theorem soundness {Atom Ag : Type} (phi psi : Formula Atom Ag) (d : ST_Entails phi psi) : 
  ST_SemanticEntails phi psi := by
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

end PEL4
