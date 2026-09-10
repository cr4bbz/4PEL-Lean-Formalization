import PEL4.MaximalClassicalLawFragment

namespace PEL4

/-!
# Gate 16: independent classical probabilistic-epistemic semantics

Unlike Gate 8's evaluator, this model type does not store two support channels
and is not definitionally a 4-PEL model. Atomic values and all formula values
are Boolean. Belief uses the positive extension, knowledge is ordinary finite
universal accessibility, and possibility is finite existential accessibility.

The projection and embedding below are comparison maps between two independently
defined semantic types. Their existence is not a completeness theorem.
-/

/-- Independent finite classical probabilistic-epistemic model. -/
structure ClassicalModalModel
    (W Ag Atom : Type) [DecidableEq W] where
  worlds : FiniteSet W
  R : Ag -> W -> FiniteSet W
  mu : Ag -> W -> ProbMeasure W
  val : W -> Atom -> Bool
  c : Ag -> Rat
  mu_total : forall (i : Ag) (w : W), mu i w (R i w) = 1
  mu_empty : forall (i : Ag) (w : W), mu i w [] = 0
  c_gt_half : forall i, c i > 1 / 2
  c_le_one : forall i, c i <= 1

/-- Standard two-valued evaluation on the independent classical model. -/
def evalClassicalModal
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom) :
    W -> ModalFormula Atom Ag -> Bool
  | w, .prop p => m.val w p
  | w, .not phi => !(evalClassicalModal m w phi)
  | w, .and phi psi =>
      evalClassicalModal m w phi && evalClassicalModal m w psi
  | w, .bel i phi =>
      m.mu i w
        (filterWorlds (m.R i w)
          (fun u => evalClassicalModal m u phi)) >= m.c i
  | w, .know i phi =>
      (m.R i w).all (fun u => evalClassicalModal m u phi)
  | w, .poss i phi =>
      (m.R i w).any (fun u => evalClassicalModal m u phi)

/-- The positive-support projection of a 4-PEL model into the independent
classical model type. -/
def Model.classicalProjection
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : ClassicalModalModel W Ag Atom where
  worlds := m.worlds
  R := m.R
  mu := m.mu
  val := fun w p => (m.val w p).pos
  c := m.c
  mu_total := m.mu_total
  mu_empty := m.mu_empty
  c_gt_half := m.c_gt_half
  c_le_one := m.c_le_one

/-- Embed a classical model into 4-PEL by placing every Boolean atom on the
classical anti-diagonal. -/
def ClassicalModalModel.fdeEmbedding
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom) : Model W Ag Atom where
  worlds := m.worlds
  R := m.R
  mu := m.mu
  val := fun w p => FDEValue.ofClassicalBool (m.val w p)
  c := m.c
  mu_total := m.mu_total
  mu_empty := m.mu_empty
  c_gt_half := m.c_gt_half
  c_le_one := m.c_le_one

/-- Strong finite probability integrity for the independent model type. -/
def ClassicalModelProbabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom) : Prop :=
  forall (i : Ag) (w : W),
    FiniteProbabilityIntegrity (m.mu i w) (m.R i w)

theorem classicalProjection_preserves_probabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (h : ModelProbabilityIntegrity m) :
    ClassicalModelProbabilityIntegrity m.classicalProjection := h

theorem fdeEmbedding_preserves_probabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (m : ClassicalModalModel W Ag Atom)
    (h : ClassicalModelProbabilityIntegrity m) :
    ModelProbabilityIntegrity m.fdeEmbedding := h

/-! ## Finite-list congruence helpers -/

theorem list_filter_congr_on_mem
    {W : Type} (xs : List W) (f g : W -> Bool)
    (h : forall x, x ∈ xs -> f x = g x) :
    xs.filter f = xs.filter g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx := h x (by simp)
      have hrest : forall y, y ∈ rest -> f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.filter_cons]
      rw [hx, ih hrest]

theorem list_all_congr_on_mem
    {W : Type} (xs : List W) (f g : W -> Bool)
    (h : forall x, x ∈ xs -> f x = g x) :
    xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx := h x (by simp)
      have hrest : forall y, y ∈ rest -> f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.all_cons]
      rw [hx, ih hrest]

theorem list_any_congr_on_mem
    {W : Type} (xs : List W) (f g : W -> Bool)
    (h : forall x, x ∈ xs -> f x = g x) :
    xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      have hx := h x (by simp)
      have hrest : forall y, y ∈ rest -> f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp only [List.any_cons]
      rw [hx, ih hrest]

/-! ## Formula-specific comparison theorem -/

/-- On the maximal recursive classical fragment, independent classical
evaluation is exactly the positive support bit of 4-PEL evaluation. -/
theorem evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    forall w,
      ModalFormula.CompositionallyClassicalAt m w phi ->
      evalClassicalModal m.classicalProjection w phi =
        (evalModal m w phi).pos := by
  induction phi with
  | prop p =>
      intro w h
      rfl
  | not phi ih =>
      intro w h
      have hClassical : IsClassicalValue (evalModal m w phi) :=
        evalModal_isClassical_of_compositionallyClassicalAt m phi w h
      have hNeg := classicalValue_neg_eq_not_pos
        (evalModal m w phi) hClassical
      simp only [evalClassicalModal, evalModal, FDEValue.not]
      change Bool.not (evalClassicalModal m.classicalProjection w phi) =
        (evalModal m w phi).neg
      rw [ih w h, hNeg]
  | and phi psi ihPhi ihPsi =>
      intro w h
      simp only [evalClassicalModal, evalModal]
      change
        (evalClassicalModal m.classicalProjection w phi &&
            evalClassicalModal m.classicalProjection w psi) =
          ((evalModal m w phi).pos && (evalModal m w psi).pos)
      rw [ihPhi w h.1, ihPsi w h.2]
  | bel i phi ih =>
      intro w h
      simp only [evalClassicalModal, evalModal, Model.classicalProjection]
      change
        decide (m.mu i w
            (filterWorlds (m.R i w)
              (fun u => evalClassicalModal m.classicalProjection u phi)) >=
            m.c i) =
          (belief m i w (fun u => evalModal m u phi)).pos
      simp only [belief]
      change
        decide (m.mu i w
            (filterWorlds (m.R i w)
              (fun u => evalClassicalModal m.classicalProjection u phi)) >=
            m.c i) =
          decide (m.mu i w
              (filterWorlds (m.R i w)
                (fun u => (evalModal m u phi).pos)) >= m.c i)
      have hFilter :
          filterWorlds (m.R i w)
              (fun u => evalClassicalModal m.classicalProjection u phi) =
            filterWorlds (m.R i w)
              (fun u => (evalModal m u phi).pos) := by
        unfold filterWorlds
        apply list_filter_congr_on_mem
        intro u hu
        exact ih u (h.1 u hu)
      rw [hFilter]
  | know i phi ih =>
      intro w h
      have hAllEq :
          (m.R i w).all
              (fun u => evalClassicalModal m.classicalProjection u phi) =
            (m.R i w).all (fun u => (evalModal m u phi).pos) := by
        apply list_all_congr_on_mem
        intro u hu
        exact ih u (h u hu)
      cases hAll : (m.R i w).all (fun u => (evalModal m u phi).pos) with
      | false =>
          simp only [evalClassicalModal, evalModal]
          change
            (m.R i w).all
                (fun u => evalClassicalModal m.classicalProjection u phi) =
              ((m.R i w).all (fun u => (evalModal m u phi).pos) &&
                modalAccessibleValueStable (m.R i w)
                  (fun u => evalModal m u phi))
          rw [hAllEq, hAll]
          rfl
      | true =>
          have hAllT : forall u, u ∈ m.R i w ->
              evalModal m u phi = FDEValue.T := by
            intro u hu
            have hPos : (evalModal m u phi).pos = true :=
              (List.all_eq_true.mp hAll) u hu
            rcases evalModal_isClassical_of_compositionallyClassicalAt
                m phi u (h u hu) with hT | hF
            · exact hT
            · rw [hF] at hPos
              contradiction
          have hStable :
              modalAccessibleValueStable (m.R i w)
                (fun u => evalModal m u phi) = true :=
            modal_stability_of_constant_profile
              (m.R i w) (fun u => evalModal m u phi)
              FDEValue.T hAllT
          simp only [evalClassicalModal, evalModal]
          change
            (m.R i w).all
                (fun u => evalClassicalModal m.classicalProjection u phi) =
              ((m.R i w).all (fun u => (evalModal m u phi).pos) &&
                modalAccessibleValueStable (m.R i w)
                  (fun u => evalModal m u phi))
          rw [hAllEq, hAll, hStable]
          rfl
  | poss i phi ih =>
      intro w h
      simp only [evalClassicalModal, evalModal]
      change
        (m.R i w).any
            (fun u => evalClassicalModal m.classicalProjection u phi) =
          (m.R i w).any (fun u => (evalModal m u phi).pos)
      apply list_any_congr_on_mem
      intro u hu
      exact ih u (h u hu)

/-- Reconstruction form: on the recovered sector the complete FDE value is
the classical embedding of the independent Boolean evaluation. -/
theorem evalModal_eq_ofClassical_evalClassicalProjection
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (w : W)
    (phi : ModalFormula Atom Ag)
    (h : ModalFormula.CompositionallyClassicalAt m w phi) :
    evalModal m w phi =
      FDEValue.ofClassicalBool
        (evalClassicalModal m.classicalProjection w phi) := by
  have hClassical :=
    evalModal_isClassical_of_compositionallyClassicalAt m phi w h
  have hPos :=
    evalClassicalProjection_eq_pos_of_compositionallyClassicalAt
      m phi w h
  rcases hClassical with hT | hF
  · rw [hT]
    rw [hT] at hPos
    change evalClassicalModal m.classicalProjection w phi = true at hPos
    rw [hPos]
    rfl
  · rw [hF]
    rw [hF] at hPos
    change evalClassicalModal m.classicalProjection w phi = false at hPos
    rw [hPos]
    rfl

end PEL4
