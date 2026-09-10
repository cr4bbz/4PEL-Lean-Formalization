import PEL4.IndependentClassicalModalSemantics

namespace PEL4

/-!
# Gate 17: recovered classical consequence equivalence

This gate proves preservation and reflection, not an unrestricted collapse.
Both compared formulas must belong to the maximal recursive classical sector.
Outside that sector the independent Boolean semantics deliberately forgets the
second 4-PEL support coordinate.
-/

/-- Ordinary truth-preserving consequence in one independent classical model. -/
def ClassicalModalSemanticEntailsIn
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom)
    (phi psi : ModalFormula Atom Ag) : Prop :=
  forall w,
    evalClassicalModal m w phi = true ->
      evalClassicalModal m w psi = true

/-- Strict classical truth is preserved and reflected by projection on the
recovered sector. -/
theorem evalClassicalProjection_true_iff_evalModal_T
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag)
    (hPhi : ModalFormula.CompositionallyClassicalAt m w phi) :
    evalClassicalModal m.classicalProjection w phi = true <->
      evalModal m w phi = FDEValue.T := by
  have hReconstruct :=
    evalModal_eq_ofClassical_evalClassicalProjection m w phi hPhi
  constructor
  · intro hTrue
    rw [hReconstruct, hTrue]
    rfl
  · intro hT
    have hPos :=
      evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
        m phi w hPhi
    rw [hT] at hPos
    exact hPos

/-- Classical falsity is likewise preserved and reflected. -/
theorem evalClassicalProjection_false_iff_evalModal_F
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag)
    (hPhi : ModalFormula.CompositionallyClassicalAt m w phi) :
    evalClassicalModal m.classicalProjection w phi = false <->
      evalModal m w phi = FDEValue.F := by
  have hReconstruct :=
    evalModal_eq_ofClassical_evalClassicalProjection m w phi hPhi
  constructor
  · intro hFalse
    rw [hReconstruct, hFalse]
    rfl
  · intro hF
    have hPos :=
      evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
        m phi w hPhi
    rw [hF] at hPos
    exact hPos

/-- Gate-17 model-relative conservativity for tolerant/LP consequence. -/
theorem modalLP_iff_classicalProjection_entails_of_recovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi psi : ModalFormula Atom Ag)
    (hPhi : ModalFormula.CompositionallyClassical m phi)
    (hPsi : ModalFormula.CompositionallyClassical m psi) :
    ModalLP_SemanticEntailsIn m phi psi <->
      ClassicalModalSemanticEntailsIn m.classicalProjection phi psi := by
  constructor
  · intro hLP w hClassicalPhi
    have hPhiPos : (evalModal m w phi).pos = true := by
      rw [← evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
        m phi w (hPhi w)]
      exact hClassicalPhi
    have hPsiPos := hLP w hPhiPos
    rw [evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
      m psi w (hPsi w)]
    exact hPsiPos
  · intro hClassical w hPhiPos
    have hClassicalPhi :
        evalClassicalModal m.classicalProjection w phi = true := by
      rw [evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
        m phi w (hPhi w)]
      exact hPhiPos
    have hClassicalPsi := hClassical w hClassicalPhi
    rw [evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
      m psi w (hPsi w)] at hClassicalPsi
    exact hClassicalPsi

/-- Under probability integrity, strict-to-tolerant 4-PEL consequence, LP
consequence, and ordinary classical consequence all coincide on the recovered
fragment. -/
theorem modalST_iff_LP_iff_classicalProjection_entails_of_recovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi psi : ModalFormula Atom Ag)
    (hPhi : ModalFormula.CompositionallyClassical m phi)
    (hPsi : ModalFormula.CompositionallyClassical m psi) :
    (ModalST_SemanticEntailsIn m phi psi <->
      ModalLP_SemanticEntailsIn m phi psi) /\
    (ModalLP_SemanticEntailsIn m phi psi <->
      ClassicalModalSemanticEntailsIn m.classicalProjection phi psi) := by
  have hRecovery : ModalFormula.CompositionalRecovery m phi :=
    (compositionalRecovery_iff_compositionallyClassical
      m hIntegrity phi).2 hPhi
  exact ⟨
    modalST_iff_LP_of_compositionalRecovery
      m hIntegrity phi psi hRecovery,
    modalLP_iff_classicalProjection_entails_of_recovery
      m phi psi hPhi hPsi⟩

/-! ## Independent-model round trip -/

/-- Embedding an independent classical model in 4-PEL and projecting it back
does not change classical evaluation. -/
theorem evalClassicalModal_projection_fdeEmbedding
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    forall w,
      evalClassicalModal m.fdeEmbedding.classicalProjection w phi =
        evalClassicalModal m w phi := by
  induction phi with
  | prop p =>
      intro w
      cases h : m.val w p <;>
        simp [evalClassicalModal, Model.classicalProjection,
          ClassicalModalModel.fdeEmbedding, FDEValue.ofClassicalBool, h]
      all_goals rfl
  | not phi ih =>
      intro w
      simp only [evalClassicalModal]
      rw [ih w]
  | and phi psi ihPhi ihPsi =>
      intro w
      simp only [evalClassicalModal]
      rw [ihPhi w, ihPsi w]
  | bel i phi ih =>
      intro w
      simp only [evalClassicalModal]
      have hFilter :
          filterWorlds (m.fdeEmbedding.classicalProjection.R i w)
              (fun u =>
                evalClassicalModal
                  m.fdeEmbedding.classicalProjection u phi) =
            filterWorlds (m.R i w)
              (fun u => evalClassicalModal m u phi) := by
        unfold filterWorlds
        apply list_filter_congr_on_mem
        intro u hu
        exact ih u
      rw [hFilter]
      rfl
  | know i phi ih =>
      intro w
      simp only [evalClassicalModal, Model.classicalProjection,
        ClassicalModalModel.fdeEmbedding]
      apply list_all_congr_on_mem
      intro u hu
      exact ih u
  | poss i phi ih =>
      intro w
      simp only [evalClassicalModal, Model.classicalProjection,
        ClassicalModalModel.fdeEmbedding]
      apply list_any_congr_on_mem
      intro u hu
      exact ih u

/-- Consequence equivalence stated from the independent-model side. Recovery
of the embedded formulas is the exact guard needed by the four-valued belief
and evidence-stable knowledge operators. -/
theorem modalLP_fdeEmbedding_iff_independentClassical_entails
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom)
    (phi psi : ModalFormula Atom Ag)
    (hPhi : ModalFormula.CompositionallyClassical m.fdeEmbedding phi)
    (hPsi : ModalFormula.CompositionallyClassical m.fdeEmbedding psi) :
    ModalLP_SemanticEntailsIn m.fdeEmbedding phi psi <->
      ClassicalModalSemanticEntailsIn m phi psi := by
  rw [modalLP_iff_classicalProjection_entails_of_recovery
    m.fdeEmbedding phi psi hPhi hPsi]
  constructor
  · intro h w hPhiTrue
    have hProjectedPhi :
        evalClassicalModal m.fdeEmbedding.classicalProjection w phi = true := by
      rw [evalClassicalModal_projection_fdeEmbedding m phi w]
      exact hPhiTrue
    have hProjectedPsi := h w hProjectedPhi
    rw [evalClassicalModal_projection_fdeEmbedding m psi w] at hProjectedPsi
    exact hProjectedPsi
  · intro h w hProjectedPhi
    have hPhiTrue : evalClassicalModal m w phi = true := by
      rw [← evalClassicalModal_projection_fdeEmbedding m phi w]
      exact hProjectedPhi
    have hPsiTrue := h w hPhiTrue
    rw [evalClassicalModal_projection_fdeEmbedding m psi w]
    exact hPsiTrue

end PEL4
