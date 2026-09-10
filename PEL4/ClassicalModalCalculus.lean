import PEL4.RecoveredClassicalConsequenceEquivalence

namespace PEL4

/-!
# Gate 18: an independent classical modal calculus and soundness

The calculus is defined directly over `ModalFormula`, but its semantic target
is the independently defined Boolean `ClassicalModalModel`. Belief monotonicity
is sound only over the strong finite-probability class because the legacy weak
measure interface does not include monotonicity.

This gate proves soundness. It does not claim completeness, decidability, proof
normalization, or a canonical-model theorem.
-/

/-- Classical material implication in the shared modal syntax. -/
def ModalFormula.implies {Atom Ag : Type}
    (phi psi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.or (ModalFormula.not phi) psi

theorem evalClassicalModal_or
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom) (w : W)
    (phi psi : ModalFormula Atom Ag) :
    evalClassicalModal m w (ModalFormula.or phi psi) =
      (evalClassicalModal m w phi || evalClassicalModal m w psi) := by
  cases hPhi : evalClassicalModal m w phi <;>
    cases hPsi : evalClassicalModal m w psi <;>
      simp [ModalFormula.or, evalClassicalModal, hPhi, hPsi]

theorem evalClassicalModal_implies
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom) (w : W)
    (phi psi : ModalFormula Atom Ag) :
    evalClassicalModal m w (ModalFormula.implies phi psi) =
      (!evalClassicalModal m w phi || evalClassicalModal m w psi) := by
  rw [ModalFormula.implies, evalClassicalModal_or]
  rfl

/-- Natural-deduction-style single-premise calculus. Modal monotonicity rules
lift already derivable global implications through `K`, raw possibility, and
Lockean belief. -/
inductive ClassicalModalDerives {Atom Ag : Type} :
    ModalFormula Atom Ag -> ModalFormula Atom Ag -> Type where
  | id (phi) : ClassicalModalDerives phi phi
  | cut : ClassicalModalDerives phi psi ->
      ClassicalModalDerives psi chi -> ClassicalModalDerives phi chi
  | doubleNegIntro (phi) :
      ClassicalModalDerives phi (ModalFormula.not (ModalFormula.not phi))
  | doubleNegElim (phi) :
      ClassicalModalDerives (ModalFormula.not (ModalFormula.not phi)) phi
  | andElimLeft (phi psi) :
      ClassicalModalDerives (ModalFormula.and phi psi) phi
  | andElimRight (phi psi) :
      ClassicalModalDerives (ModalFormula.and phi psi) psi
  | andIntro : ClassicalModalDerives phi psi ->
      ClassicalModalDerives phi chi ->
      ClassicalModalDerives phi (ModalFormula.and psi chi)
  | orIntroLeft (phi psi) :
      ClassicalModalDerives phi (ModalFormula.or phi psi)
  | orIntroRight (phi psi) :
      ClassicalModalDerives psi (ModalFormula.or phi psi)
  | excludedMiddle (premise phi) :
      ClassicalModalDerives premise (ModalFormula.excludedMiddle phi)
  | explosion (phi conclusion) :
      ClassicalModalDerives (ModalFormula.contradiction phi) conclusion
  | modusPonens (phi psi) :
      ClassicalModalDerives
        (ModalFormula.and phi (ModalFormula.implies phi psi)) psi
  | contraposition : ClassicalModalDerives phi psi ->
      ClassicalModalDerives (ModalFormula.not psi) (ModalFormula.not phi)
  | knowMono (i : Ag) (phi psi : ModalFormula Atom Ag) :
      ClassicalModalDerives phi psi ->
      ClassicalModalDerives (ModalFormula.know i phi) (ModalFormula.know i psi)
  | possMono (i : Ag) (phi psi : ModalFormula Atom Ag) :
      ClassicalModalDerives phi psi ->
      ClassicalModalDerives (ModalFormula.poss i phi) (ModalFormula.poss i psi)
  | belMono (i : Ag) (phi psi : ModalFormula Atom Ag) :
      ClassicalModalDerives phi psi ->
      ClassicalModalDerives (ModalFormula.bel i phi) (ModalFormula.bel i psi)

/-- Global semantic consequence over independent classical models satisfying
finite probability integrity. -/
def StrongClassicalModalSemanticEntails {Atom Ag : Type}
    (phi psi : ModalFormula Atom Ag) : Prop :=
  forall {W : Type} [DecidableEq W]
      (m : ClassicalModalModel W Ag Atom),
    ClassicalModelProbabilityIntegrity m ->
      ClassicalModalSemanticEntailsIn m phi psi

/-- Gate-18 soundness theorem. -/
theorem classicalModalCalculus_soundness
    {Atom Ag : Type} {phi psi : ModalFormula Atom Ag}
    (d : ClassicalModalDerives phi psi) :
    StrongClassicalModalSemanticEntails phi psi := by
  induction d with
  | id phi =>
      intro W _ m hIntegrity w hPhi
      exact hPhi
  | cut dPhiPsi dPsiChi ihPhiPsi ihPsiChi =>
      intro W _ m hIntegrity w hPhi
      exact ihPsiChi m hIntegrity w (ihPhiPsi m hIntegrity w hPhi)
  | doubleNegIntro phi =>
      intro W _ m hIntegrity w hPhi
      simp [evalClassicalModal, hPhi]
  | doubleNegElim phi =>
      intro W _ m hIntegrity w hPhi
      simpa [evalClassicalModal] using hPhi
  | andElimLeft phi psi =>
      intro W _ m hIntegrity w hAnd
      change
        (evalClassicalModal m w phi && evalClassicalModal m w psi) = true
          at hAnd
      simp at hAnd
      exact hAnd.1
  | andElimRight phi psi =>
      intro W _ m hIntegrity w hAnd
      change
        (evalClassicalModal m w phi && evalClassicalModal m w psi) = true
          at hAnd
      simp at hAnd
      exact hAnd.2
  | andIntro dPhiPsi dPhiChi ihPhiPsi ihPhiChi =>
      intro W _ m hIntegrity w hPhi
      change
        (evalClassicalModal m w _ && evalClassicalModal m w _) = true
      have hPsi := ihPhiPsi m hIntegrity w hPhi
      have hChi := ihPhiChi m hIntegrity w hPhi
      simp [hPsi, hChi]
  | orIntroLeft phi psi =>
      intro W _ m hIntegrity w hPhi
      rw [evalClassicalModal_or]
      simp [hPhi]
  | orIntroRight phi psi =>
      intro W _ m hIntegrity w hPsi
      rw [evalClassicalModal_or]
      simp [hPsi]
  | excludedMiddle premise phi =>
      intro W _ m hIntegrity w hPremise
      rw [ModalFormula.excludedMiddle, evalClassicalModal_or]
      cases h : evalClassicalModal m w phi <;> simp [evalClassicalModal, h]
  | explosion phi conclusion =>
      intro W _ m hIntegrity w hContradiction
      change
        (evalClassicalModal m w phi &&
          !evalClassicalModal m w phi) = true at hContradiction
      cases h : evalClassicalModal m w phi <;> simp [h] at hContradiction
  | modusPonens phi psi =>
      intro W _ m hIntegrity w hPremise
      change
        (evalClassicalModal m w phi &&
          evalClassicalModal m w (ModalFormula.implies phi psi)) = true
            at hPremise
      have hParts :
          evalClassicalModal m w phi = true /\
          evalClassicalModal m w (ModalFormula.implies phi psi) = true := by
        simpa using hPremise
      rw [evalClassicalModal_implies, hParts.1] at hParts
      simpa using hParts.2
  | contraposition d ih =>
      intro W _ m hIntegrity w hNotPsi
      change (!evalClassicalModal m w _) = true at hNotPsi
      change (!evalClassicalModal m w _) = true
      cases hPhi : evalClassicalModal m w _ with
      | false => simp
      | true =>
          have hPsi := ih m hIntegrity w hPhi
          rw [hPsi] at hNotPsi
          contradiction
  | knowMono i phi psi d ih =>
      intro W _ m hIntegrity w hKnowPhi
      change
        (m.R i w).all (fun u => evalClassicalModal m u _) = true
          at hKnowPhi ⊢
      rw [List.all_eq_true] at hKnowPhi ⊢
      intro u hu
      exact ih m hIntegrity u (hKnowPhi u hu)
  | possMono i phi psi d ih =>
      intro W _ m hIntegrity w hPossPhi
      change
        (m.R i w).any (fun u => evalClassicalModal m u _) = true
          at hPossPhi ⊢
      rw [List.any_eq_true] at hPossPhi ⊢
      rcases hPossPhi with ⟨u, hu, hPhi⟩
      exact ⟨u, hu, ih m hIntegrity u hPhi⟩
  | belMono i phi psi d ih =>
      intro W _ m hIntegrity w hBelPhi
      let sourceEvent :=
        filterWorlds (m.R i w) (fun u => evalClassicalModal m u phi)
      let targetEvent :=
        filterWorlds (m.R i w) (fun u => evalClassicalModal m u psi)
      have hSourceNodup : sourceEvent.Nodup := by
        exact filterWorlds_nodup _ _ (hIntegrity i w).support_nodup
      have hTargetNodup : targetEvent.Nodup := by
        exact filterWorlds_nodup _ _ (hIntegrity i w).support_nodup
      have hSubset : FiniteEventSubset sourceEvent targetEvent := by
        intro u hu
        have huSource := List.mem_filter.mp hu
        apply List.mem_filter.mpr
        exact ⟨huSource.1, ih m hIntegrity u huSource.2⟩
      have hTargetSubset : FiniteEventSubset targetEvent (m.R i w) := by
        intro u hu
        exact (List.mem_filter.mp hu).1
      have hMassMono : m.mu i w sourceEvent <= m.mu i w targetEvent :=
        (hIntegrity i w).monotone sourceEvent targetEvent
          hSourceNodup hTargetNodup hSubset hTargetSubset
      change decide (m.mu i w sourceEvent >= m.c i) = true at hBelPhi
      change decide (m.mu i w targetEvent >= m.c i) = true
      have hSourceThreshold : m.c i <= m.mu i w sourceEvent :=
        of_decide_eq_true hBelPhi
      have hTargetThreshold : m.c i <= m.mu i w targetEvent :=
        Rat.le_trans hSourceThreshold hMassMono
      exact decide_eq_true hTargetThreshold

/-! ## Transfer back to recovered 4-PEL -/

/-- Every classical derivation transports soundly to LP consequence in a
recovered integrity-certified 4-PEL model. -/
theorem classicalModalDerivation_sound_in_recovered_4PEL_LP
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    {phi psi : ModalFormula Atom Ag}
    (d : ClassicalModalDerives phi psi)
    (hPhi : ModalFormula.CompositionallyClassical m phi)
    (hPsi : ModalFormula.CompositionallyClassical m psi) :
    ModalLP_SemanticEntailsIn m phi psi := by
  apply (modalLP_iff_classicalProjection_entails_of_recovery
    m phi psi hPhi hPsi).2
  exact classicalModalCalculus_soundness d
    m.classicalProjection
    (classicalProjection_preserves_probabilityIntegrity m hIntegrity)

/-- The same derivation is sound for recovered ST consequence. -/
theorem classicalModalDerivation_sound_in_recovered_4PEL_ST
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    {phi psi : ModalFormula Atom Ag}
    (d : ClassicalModalDerives phi psi)
    (hPhi : ModalFormula.CompositionallyClassical m phi)
    (hPsi : ModalFormula.CompositionallyClassical m psi) :
    ModalST_SemanticEntailsIn m phi psi := by
  have hLP := classicalModalDerivation_sound_in_recovered_4PEL_LP
    m hIntegrity d hPhi hPsi
  exact ModalLP_SemanticEntailsIn_implies_ST m phi psi hLP

/-! ## Why belief monotonicity uses the strong model class -/

def gate18WeakBeliefModel : ClassicalModalModel (Fin 3) Unit Bool where
  worlds := [0, 1, 2]
  R := fun _ _ => [0, 1, 2]
  mu := fun _ _ S =>
    if S = [0, 1, 2] then 1 else if S = [0] then 1 else 0
  val := fun w p => if p then w = 1 else w = 0
  c := fun _ => 3 / 4
  mu_total := by intro _ _; decide +kernel
  mu_empty := by intro _ _; decide +kernel
  c_gt_half := by intro _; decide +kernel
  c_le_one := by intro _; decide +kernel

def gate18P : ModalFormula Bool Unit := .prop false
def gate18Q : ModalFormula Bool Unit := .prop true

/-- Propositional weakening `p -> p or q` is derivable. -/
def gate18PDerivesPOrQ :
    ClassicalModalDerives gate18P (ModalFormula.or gate18P gate18Q) :=
  ClassicalModalDerives.orIntroLeft gate18P gate18Q

/-- The weak legacy measure contract is insufficient for the belief
monotonicity rule: the source event can have mass one while its larger target
event has mass zero. -/
theorem gate18_belief_monotonicity_fails_without_integrity :
    ¬ ClassicalModalSemanticEntailsIn gate18WeakBeliefModel
      (ModalFormula.bel () gate18P)
      (ModalFormula.bel () (ModalFormula.or gate18P gate18Q)) := by
  intro h
  have hSource :
      evalClassicalModal gate18WeakBeliefModel 0
        (ModalFormula.bel () gate18P) = true := by
    decide +kernel
  have hTarget :
      evalClassicalModal gate18WeakBeliefModel 0
        (ModalFormula.bel () (ModalFormula.or gate18P gate18Q)) = false := by
    decide +kernel
  have hFailure := h 0 hSource
  rw [hTarget] at hFailure
  contradiction

end PEL4
