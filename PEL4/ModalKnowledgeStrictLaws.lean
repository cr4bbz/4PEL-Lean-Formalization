import PEL4.ModalKnowledgeLaws

namespace PEL4

/-!
# Strict modal laws of evidence-stable knowledge

The first modal-law gate showed that positive introspection fails without frame
conditions, while identical successor neighborhoods recover it.  This module
separates the strict `T` fragment from the merely positive/designated fragment.

The strict fragment is structurally better behaved.  If `K phi = T`, then every
accessible evaluation of `phi` must itself be exactly `T`: positive support is
universal, instability is absent, and accessible negative support is absent.
This yields two natural recovery laws:

* strict conjunction decomposition without any frame condition;
* strict positive introspection under ordinary local transitivity.
-/

/-- A finite profile that is pointwise constant is value-stable. -/
theorem modal_stability_of_constant_profile
    {W : Type} [DecidableEq W]
    (worlds : FiniteSet W) (value : W → FDEValue) (v : FDEValue)
    (hConst : ∀ x, x ∈ worlds → value x = v) :
    modalAccessibleValueStable worlds value = true := by
  cases worlds with
  | nil =>
      rfl
  | cons first rest =>
      unfold modalAccessibleValueStable
      simp only [List.all_eq_true]
      intro x hx
      have hFirst : value first = v := hConst first (by simp)
      have hX : value x = v := hConst x (by simp [hx])
      rw [hX, hFirst]
      simp

/-- If every accessible point gives `phi` strict value `T`, then evidence-stable
knowledge of `phi` is itself strict `T`.  This also covers the empty range,
where the modal knowledge definition is vacuously `T`. -/
theorem modal_strict_knowledge_of_all_accessible_strict_true
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hAllT : ∀ u, u ∈ m.R i w → evalModal m u phi = FDEValue.T) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.T := by
  have hStable :
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) = true :=
    modal_stability_of_constant_profile
      (m.R i w) (fun u => evalModal m u phi) FDEValue.T hAllT
  have hAllPos :
      (m.R i w).all (fun u => (evalModal m u phi).pos) = true := by
    simp only [List.all_eq_true]
    intro u hu
    rw [hAllT u hu]
    rfl
  have hAnyNeg :
      (m.R i w).any (fun u => (evalModal m u phi).neg) = false := by
    cases hAny : (m.R i w).any (fun u => (evalModal m u phi).neg) with
    | false =>
        rfl
    | true =>
        have hWitness : ∃ u ∈ m.R i w, (evalModal m u phi).neg = true := by
          simpa only [List.any_eq_true] using hAny
        rcases hWitness with ⟨u, hu, hNeg⟩
        rw [hAllT u hu] at hNeg
        change false = true at hNeg
        cases hNeg
  change modalKnowledgeValue m i w (fun u => evalModal m u phi) = FDEValue.T
  simp [modalKnowledgeValue, hStable, hAllPos, hAnyNeg, FDEValue.T]

/-- Strict knowledge makes the formula strictly true at every accessible point.
This is stronger than reflexive factivity: no reflexivity assumption is needed
because the conclusion concerns the accessible range itself. -/
theorem modal_accessible_strict_truth_of_strict_knowledge
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hK : evalModal m w (ModalFormula.know i phi) = FDEValue.T) :
    ∀ u, u ∈ m.R i w → evalModal m u phi = FDEValue.T := by
  have hKPos :
      (evalModal m w (ModalFormula.know i phi)).pos = true := by
    rw [hK]
    rfl
  have hKNeg :
      (evalModal m w (ModalFormula.know i phi)).neg = false := by
    rw [hK]
    rfl
  change ((m.R i w).all (fun u => (evalModal m u phi).pos) &&
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi)) = true at hKPos
  have hAllPos :
      (m.R i w).all (fun u => (evalModal m u phi).pos) = true := by
    cases hAll : (m.R i w).all (fun u => (evalModal m u phi).pos) <;>
      cases hStable : modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) <;> simp_all
  change ((!modalAccessibleValueStable (m.R i w)
      (fun u => evalModal m u phi)) ||
      (m.R i w).any (fun u => (evalModal m u phi).neg)) = false at hKNeg
  have hAnyNeg :
      (m.R i w).any (fun u => (evalModal m u phi).neg) = false := by
    cases hStable : modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) <;>
      cases hAny : (m.R i w).any (fun u => (evalModal m u phi).neg) <;>
      simp_all
  intro u hu
  have hPos : (evalModal m u phi).pos = true := by
    simp only [List.all_eq_true] at hAllPos
    exact hAllPos u hu
  have hNeg : (evalModal m u phi).neg = false := by
    cases hn : (evalModal m u phi).neg with
    | false =>
        rfl
    | true =>
        have hAnyTrue :
            (m.R i w).any (fun x => (evalModal m x phi).neg) = true := by
          simp only [List.any_eq_true]
          exact ⟨u, hu, hn⟩
        rw [hAnyNeg] at hAnyTrue
        cases hAnyTrue
  cases hVal : evalModal m u phi with
  | mk pos neg =>
      cases pos <;> cases neg <;> simp_all [FDEValue.T]

/-- At the FDE level, strict truth of a conjunction forces strict truth of both
conjuncts. -/
theorem fde_strict_conjunction_decomposes
    (v₁ v₂ : FDEValue)
    (h : FDEValue.and v₁ v₂ = FDEValue.T) :
    v₁ = FDEValue.T ∧ v₂ = FDEValue.T := by
  rcases v₁ with ⟨p₁, n₁⟩
  rcases v₂ with ⟨p₂, n₂⟩
  cases p₁ <;> cases n₁ <;> cases p₂ <;> cases n₂ <;>
    simp_all [FDEValue.and, FDEValue.T]

/-- Strict evidence-stable knowledge of a conjunction decomposes into strict
knowledge of both conjuncts with no frame assumption.

This sharply contrasts with the already verified positive/designated failure
`K+ (phi and psi) -/-> K+ phi`: that failure lives in the non-strict phase. -/
theorem modal_strict_knowledge_conjunction_decomposes
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : ModalFormula Atom Ag)
    (hK : evalModal m w
      (ModalFormula.know i (ModalFormula.and phi psi)) = FDEValue.T) :
    evalModal m w (ModalFormula.know i phi) = FDEValue.T ∧
      evalModal m w (ModalFormula.know i psi) = FDEValue.T := by
  have hAllConj :=
    modal_accessible_strict_truth_of_strict_knowledge
      m i w (ModalFormula.and phi psi) hK
  have hAllPhi : ∀ u, u ∈ m.R i w → evalModal m u phi = FDEValue.T := by
    intro u hu
    have h := hAllConj u hu
    change FDEValue.and (evalModal m u phi) (evalModal m u psi) = FDEValue.T at h
    exact (fde_strict_conjunction_decomposes
      (evalModal m u phi) (evalModal m u psi) h).1
  have hAllPsi : ∀ u, u ∈ m.R i w → evalModal m u psi = FDEValue.T := by
    intro u hu
    have h := hAllConj u hu
    change FDEValue.and (evalModal m u phi) (evalModal m u psi) = FDEValue.T at h
    exact (fde_strict_conjunction_decomposes
      (evalModal m u phi) (evalModal m u psi) h).2
  constructor
  · exact modal_strict_knowledge_of_all_accessible_strict_true
      m i w phi hAllPhi
  · exact modal_strict_knowledge_of_all_accessible_strict_true
      m i w psi hAllPsi

/-- Ordinary local transitivity at a point: every two-step successor of `w` is
already an immediate successor of `w`. -/
def ModalTransitiveAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) : Prop :=
  ∀ u, u ∈ m.R i w → ∀ v, v ∈ m.R i u → v ∈ m.R i w

/-- Strict axiom-4 recovery under ordinary transitivity.

If `K phi = T` at `w`, every immediate successor makes `phi = T`.  By
transitivity, every successor of each such successor is still in that original
strict-`T` region, so every immediate successor itself has `K phi = T`.  The
outer knowledge operator therefore also returns strict `T`. -/
theorem modal_strict_introspection_of_transitive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hK : evalModal m w (ModalFormula.know i phi) = FDEValue.T) :
    evalModal m w
      (ModalFormula.know i (ModalFormula.know i phi)) = FDEValue.T := by
  have hAllPhi :=
    modal_accessible_strict_truth_of_strict_knowledge m i w phi hK
  have hAllK : ∀ u, u ∈ m.R i w →
      evalModal m u (ModalFormula.know i phi) = FDEValue.T := by
    intro u hu
    apply modal_strict_knowledge_of_all_accessible_strict_true
    intro v hv
    exact hAllPhi v (hTrans u hu v hv)
  exact modal_strict_knowledge_of_all_accessible_strict_true
    m i w (ModalFormula.know i phi) hAllK

/-!
## Interpretation

The strict fragment now has a recognizably classical modal skeleton:

* strict `K` forces strict truth throughout the accessible range;
* strict knowledge of conjunction decomposes without any frame assumption;
* ordinary transitivity restores strict positive introspection.

This does not erase the nonclassical positive/designated layer.  The earlier
crossed-glut conjunction witness and unrestricted introspection witness remain
valid.  The emerging picture is therefore phase-sensitive: classical-looking
modal laws can reappear at strict `T` even when their merely positive analogues
fail.

The next gate should determine whether ordinary transitivity also suffices for
positive/designated introspection when `K phi = B`, and should isolate the role
played by the model's built-in nonempty accessibility forced by probability
normalization.
-/

end PEL4
