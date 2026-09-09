import PEL4.CPELClassicalCollapse
import PEL4.Soundness

namespace PEL4

/-!
# Gate 8: semantic consequence through the split CPEL representation

These consequence notions deliberately quantify only over the Boolean CPEL evaluator
induced by existing 4-PEL models.  They are not validity notions over an independently
axiomatized class of arbitrary CPEL models.
-/

/-- Positive-channel semantic consequence in the CPEL evaluator induced by 4-PEL
models. -/
def CPELPositiveSemanticEntails {Atom Ag : Type}
    (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    evalCPEL m w (tr_pos phi) = true →
      evalCPEL m w (tr_pos psi) = true

/-- Split strict-to-tolerant consequence in the induced CPEL evaluator.  Strict truth
of the antecedent is represented by positive truth together with negative falsity. -/
def CPELSplitSTSemanticEntails {Atom Ag : Type}
    (phi psi : Formula Atom Ag) : Prop :=
  ∀ {W : Type} [DecidableEq W] (m : Model W Ag Atom) (w : W),
    evalCPEL m w (tr_pos phi) = true →
    evalCPEL m w (tr_neg phi) = false →
      evalCPEL m w (tr_pos psi) = true

/-- Strict FDE truth is exactly the split Boolean profile `(true,false)`. -/
theorem eval_eq_T_iff_split_strict
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag) :
    eval m w phi = FDEValue.T ↔
      evalCPEL m w (tr_pos phi) = true ∧
      evalCPEL m w (tr_neg phi) = false := by
  rw [evalCPEL_tr_pos, evalCPEL_tr_neg]
  cases h : eval m w phi with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [FDEValue.T]

/-- LP semantic consequence is represented exactly by positive-channel consequence
in the CPEL evaluator induced by the same 4-PEL models. -/
theorem LP_SemanticEntails_iff_CPELPositiveSemanticEntails
    {Atom Ag : Type}
    (phi psi : Formula Atom Ag) :
    LP_SemanticEntails phi psi ↔
      CPELPositiveSemanticEntails phi psi := by
  constructor
  · intro h W _ m w hphi
    rw [evalCPEL_tr_pos] at hphi ⊢
    exact h m w hphi
  · intro h W _ m w hphi
    have hphiC : evalCPEL m w (tr_pos phi) = true := by
      rw [evalCPEL_tr_pos]
      exact hphi
    have hpsiC := h m w hphiC
    rw [evalCPEL_tr_pos] at hpsiC
    exact hpsiC

/-- ST semantic consequence is represented exactly by the split strict antecedent
and positive consequent in the induced CPEL evaluator. -/
theorem ST_SemanticEntails_iff_CPELSplitSTSemanticEntails
    {Atom Ag : Type}
    (phi psi : Formula Atom Ag) :
    ST_SemanticEntails phi psi ↔
      CPELSplitSTSemanticEntails phi psi := by
  constructor
  · intro h W _ m w hpos hneg
    have hstrict : eval m w phi = FDEValue.T :=
      (eval_eq_T_iff_split_strict m w phi).2 ⟨hpos, hneg⟩
    have hpsi := h m w hstrict
    rw [evalCPEL_tr_pos]
    exact hpsi
  · intro h W _ m w hstrict
    have hs := (eval_eq_T_iff_split_strict m w phi).1 hstrict
    have hpsiC := h m w hs.1 hs.2
    rw [evalCPEL_tr_pos] at hpsiC
    exact hpsiC

/-- Existing ST derivability therefore soundly transports to the induced split CPEL
semantic consequence.  This is a corollary of the repository's source soundness theorem
and the semantic representation bridge, not a completeness result for CPEL. -/
theorem ST_derivation_sound_in_induced_CPEL
    {Atom Ag : Type}
    (phi psi : Formula Atom Ag)
    (d : ST_Entails phi psi) :
    CPELSplitSTSemanticEntails phi psi :=
  (ST_SemanticEntails_iff_CPELSplitSTSemanticEntails phi psi).1
    (soundness phi psi d)

end PEL4
