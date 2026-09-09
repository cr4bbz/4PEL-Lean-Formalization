import PEL4.ProbabilityIntegrityFormulaRecovery
import PEL4.Translation
import PEL4.ModalFormulaClassicalRecovery

namespace PEL4

/-!
# Gate 8: collapse of the split CPEL translation on the recovered classical sector

The legacy translation sends positive and negative 4-PEL support into two classical
atomic channels `(p, true)` and `(p, false)`. This file gives that target syntax an
explicit Boolean semantics over an existing finite 4-PEL model and proves three facts:

1. the positive and negative CPEL translations reproduce the two FDE support bits
   exactly, even outside the recovered classical sector;
2. the pair of translated Boolean values is therefore an exact representation of the
   full four-valued evaluation;
3. classicality is exactly the locus on which the negative channel is the Boolean
   complement of the positive channel, so the two-bit representation collapses to one
   classical degree of freedom.

This is a semantic translation and representation theorem. It does not by itself
prove completeness of CPEL or a canonical-model theorem for the source logic.
-/

/-- Boolean evaluation of the split CPEL target over a 4-PEL model. The Boolean tag
on an atom selects the positive (`true`) or negative (`false`) support channel. -/
def evalCPEL {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) :
    W → CPELFormula (Atom × Bool) Ag → Bool
  | w, CPELFormula.prop (p, channel) =>
      if channel then (m.val w p).pos else (m.val w p).neg
  | w, CPELFormula.not phi => !(evalCPEL m w phi)
  | w, CPELFormula.and phi psi =>
      evalCPEL m w phi && evalCPEL m w psi
  | w, CPELFormula.bel i phi =>
      m.mu i w
        (filterWorlds (m.R i w) (fun u => evalCPEL m u phi)) ≥ m.c i

/-- The derived classical OR in CPEL evaluates as Boolean disjunction. -/
theorem evalCPEL_or
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi psi : CPELFormula (Atom × Bool) Ag) :
    evalCPEL m w (CPELFormula.or phi psi) =
      (evalCPEL m w phi || evalCPEL m w psi) := by
  cases hphi : evalCPEL m w phi <;>
    cases hpsi : evalCPEL m w psi <;>
    simp [CPELFormula.or, evalCPEL, hphi, hpsi]

/-- Exact split-translation theorem: the two CPEL translations recover the two
support bits of the original 4-PEL evaluation. No classicality assumption is used. -/
theorem evalCPEL_translation_bits
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : Formula Atom Ag) :
    ∀ w,
      evalCPEL m w (tr_pos phi) = (eval m w phi).pos ∧
      evalCPEL m w (tr_neg phi) = (eval m w phi).neg := by
  induction phi with
  | prop p =>
      intro w
      simp [tr_pos, tr_neg, evalCPEL, eval]
  | not phi ih =>
      intro w
      have h := ih w
      constructor
      · simpa [tr_pos, tr_neg, eval, FDEValue.not] using h.2
      · simpa [tr_pos, tr_neg, eval, FDEValue.not] using h.1
  | and phi psi ihPhi ihPsi =>
      intro w
      have hp := ihPhi w
      have hq := ihPsi w
      constructor
      · simp [tr_pos, evalCPEL, eval, FDEValue.and, hp.1, hq.1]
      · rw [tr_neg]
        rw [evalCPEL_or]
        simp [eval, FDEValue.and, hp.2, hq.2]
  | bel i phi ih =>
      intro w
      have hpos :
          ∀ u, evalCPEL m u (tr_pos phi) = (eval m u phi).pos :=
        fun u => (ih u).1
      have hneg :
          ∀ u, evalCPEL m u (tr_neg phi) = (eval m u phi).neg :=
        fun u => (ih u).2
      constructor
      · simp [tr_pos, evalCPEL, eval, belief, filterWorlds, hpos]
      · simp [tr_neg, evalCPEL, eval, belief, filterWorlds, hneg]

/-- Positive-channel correctness as a convenient projection of the paired theorem. -/
theorem evalCPEL_tr_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag) :
    evalCPEL m w (tr_pos phi) = (eval m w phi).pos :=
  (evalCPEL_translation_bits m phi w).1

/-- Negative-channel correctness as a convenient projection of the paired theorem. -/
theorem evalCPEL_tr_neg
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag) :
    evalCPEL m w (tr_neg phi) = (eval m w phi).neg :=
  (evalCPEL_translation_bits m phi w).2

/-- Package the two translated CPEL channels back into an FDE value. -/
def evalCPELPair
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag) : FDEValue :=
  { pos := evalCPEL m w (tr_pos phi)
    neg := evalCPEL m w (tr_neg phi) }

/-- Unconditional representation theorem: every 4-PEL formula value is exactly the
pair of its positive and negative CPEL translations. This holds on all four values,
not merely on the recovered classical slice. -/
theorem eval_eq_evalCPELPair
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag) :
    eval m w phi = evalCPELPair m w phi := by
  have hpos := evalCPEL_tr_pos m w phi
  have hneg := evalCPEL_tr_neg m w phi
  cases hEval : eval m w phi with
  | mk pos neg =>
      rw [hEval] at hpos hneg
      simp at hpos hneg
      rw [hEval]
      simp [evalCPELPair, hpos, hneg]

/-- A four-valued point is classical exactly when its negative support bit is the
Boolean complement of its positive support bit. This identifies the classical sector
inside the two-bit evidence square independently of formula syntax. -/
theorem classicalValue_iff_neg_eq_not_pos
    (v : FDEValue) :
    IsClassicalValue v ↔ v.neg = !v.pos := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [IsClassicalValue, FDEValue.T, FDEValue.F]

/-- Exact split-collapse characterization: a formula has a classical FDE value iff
the two translated CPEL channels are Boolean complements. -/
theorem isClassicalValue_iff_splitTranslations_complement
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag) :
    IsClassicalValue (eval m w phi) ↔
      evalCPEL m w (tr_neg phi) =
        !(evalCPEL m w (tr_pos phi)) := by
  rw [evalCPEL_tr_neg, evalCPEL_tr_pos]
  exact classicalValue_iff_neg_eq_not_pos (eval m w phi)

/-- On the recovered classical slice, the two split translations are semantically
redundant: the negative translation is exactly the Boolean complement of the positive
translation. -/
theorem splitTranslations_complement_of_classical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag)
    (hClassical : IsClassicalValue (eval m w phi)) :
    evalCPEL m w (tr_neg phi) =
      !(evalCPEL m w (tr_pos phi)) :=
  (isClassicalValue_iff_splitTranslations_complement m w phi).1 hClassical

/-- Reconstruct a classical FDE value from one Boolean support bit. -/
def FDEValue.ofClassicalBool (b : Bool) : FDEValue :=
  match b with
  | true => FDEValue.T
  | false => FDEValue.F

/-- Once a formula has a classical value, the positive CPEL translation alone carries
its complete FDE value. -/
theorem eval_eq_ofClassicalBool_tr_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : Formula Atom Ag)
    (hClassical : IsClassicalValue (eval m w phi)) :
    eval m w phi =
      FDEValue.ofClassicalBool (evalCPEL m w (tr_pos phi)) := by
  rcases hClassical with hT | hF
  · rw [evalCPEL_tr_pos, hT]
    rfl
  · rw [evalCPEL_tr_pos, hF]
    rfl

/-- Gate-8 collapse theorem. Under probability integrity and the Gate-7 recursive
recovery contract, the split CPEL translation collapses at every world to a single
classical Boolean degree of freedom. -/
theorem probabilityRecovery_splitTranslations_collapse
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag)
    (hRecovery : Formula.ProbabilityRecoveryAdmissible m phi) :
    ∀ w,
      evalCPEL m w (tr_neg phi) =
        !(evalCPEL m w (tr_pos phi)) := by
  intro w
  exact splitTranslations_complement_of_classical
    m w phi
    (eval_isClassical_of_probabilityRecoveryAdmissible
      m hIntegrity phi w (hRecovery w))

/-- Strong reconstruction form of Gate 8: on the recovered sector, 4-PEL evaluation
is exactly the classical FDE embedding of the positive CPEL translation. -/
theorem probabilityRecovery_eval_reconstructed_from_tr_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : Formula Atom Ag)
    (hRecovery : Formula.ProbabilityRecoveryAdmissible m phi) :
    ∀ w,
      eval m w phi =
        FDEValue.ofClassicalBool (evalCPEL m w (tr_pos phi)) := by
  intro w
  exact eval_eq_ofClassicalBool_tr_pos
    m w phi
    (eval_isClassical_of_probabilityRecoveryAdmissible
      m hIntegrity phi w (hRecovery w))

end PEL4
