import PEL4.ModalDynamicsIntermediatePhase

namespace PEL4.PaperReview

/-- Normalization excludes empty accessibility even in the lightweight model. -/
theorem accessibility_nonempty {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) : m.R i w ≠ [] := by
  intro h
  have hTotal := m.mu_total i w
  rw [h, m.mu_empty i w] at hTotal
  have hNe : (0 : Rat) ≠ 1 := by decide +kernel
  exact hNe hTotal

/-- For a fixed value interpretation, primitive K depends on accessibility,
not directly on the probability field or threshold. -/
theorem knowledge_ignores_probability_for_fixed_values
    {W Ag Atom : Type} [DecidableEq W]
    (before after : Model W Ag Atom) (i : Ag) (w : W)
    (value : W → FDEValue) (hR : after.R i w = before.R i w) :
    modalKnowledgeValue after i w value =
      modalKnowledgeValue before i w value := by
  simp only [modalKnowledgeValue, hR]

/-- With inclusive thresholding, the intersection belongs to B. -/
theorem threshold_intersection_is_B (c : Rat) :
    supportThresholdState c c c = FDEValue.B := by
  simp [supportThresholdState, FDEValue.B]

/-- Simultaneous T/F motion can have an isolated B value at the common hit.
This is a support-space witness, not an update-generated model path. -/
theorem simultaneous_T_F_has_B_hit :
    affineThresholdState (3/5) (4/5) (2/5) (2/5) (4/5) 0 = FDEValue.T ∧
    affineThresholdState (3/5) (4/5) (2/5) (2/5) (4/5) (1/2) = FDEValue.B ∧
    affineThresholdState (3/5) (4/5) (2/5) (2/5) (4/5) 1 = FDEValue.F := by
  decide +kernel

end PEL4.PaperReview
