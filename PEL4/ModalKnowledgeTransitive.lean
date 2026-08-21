import PEL4.ModalKnowledgeStrictLaws

namespace PEL4

/-!
# Positive introspection under transitivity

The strict modal-law gate verifies that ordinary local transitivity restores
strict axiom 4.  The remaining question is whether the same frame condition is
already sufficient for merely positive/designated knowledge, where `K phi` may
have value `B` rather than `T`.

A specifically 4-PEL fact matters here.  The ambient probabilistic model
structure already forces every accessibility list to be nonempty:

  mu(R_i(w)) = 1
  mu([])     = 0.

Thus a successor cannot acquire vacuous `T` knowledge from an empty
neighborhood.  Under transitivity, every successor samples a nonempty subset of
the source's already stable `phi` profile.  It therefore recovers exactly the
same `T` or `B` knowledge value.
-/

/-- Accessibility is serial in every constructible 4-PEL model.  This is not a
separate frame axiom: it follows from probability normalization together with
zero mass for the empty set. -/
theorem model_accessibility_nonempty
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) :
    m.R i w ≠ [] := by
  intro hEmpty
  have hTotal := m.mu_total i w
  have hZero := m.mu_empty i w
  rw [hEmpty] at hTotal
  have hZeroOne : (0 : Rat) = 1 := by
    calc
      (0 : Rat) = m.mu i w [] := by symm; exact hZero
      _ = 1 := hTotal
  exact (by native_decide : (0 : Rat) ≠ 1) hZeroOne

/-- A nonempty homogeneous accessible profile is recovered exactly by the
primitive knowledge operator.  Unlike the strict helper from the preceding
module, the common value may be any of `T`, `F`, `B`, or `N`. -/
theorem modal_knowledge_recovers_nonempty_constant_profile
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) (v : FDEValue)
    (hNonempty : m.R i w ≠ [])
    (hConst : ∀ u, u ∈ m.R i w → evalModal m u phi = v) :
    evalModal m w (ModalFormula.know i phi) = v := by
  have hStable :
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) = true :=
    modal_stability_of_constant_profile
      (m.R i w) (fun u => evalModal m u phi) v hConst
  have hAllPos :
      (m.R i w).all (fun u => (evalModal m u phi).pos) = v.pos := by
    cases hp : v.pos with
    | false =>
        cases hR : m.R i w with
        | nil =>
            exact False.elim (hNonempty hR)
        | cons first rest =>
            have hFirst : evalModal m first phi = v :=
              hConst first (by simp [hR])
            simp [hFirst, hp]
    | true =>
        simp only [List.all_eq_true]
        intro u hu
        rw [hConst u hu, hp]
  have hAnyNeg :
      (m.R i w).any (fun u => (evalModal m u phi).neg) = v.neg := by
    cases hn : v.neg with
    | false =>
        cases hAny : (m.R i w).any (fun u => (evalModal m u phi).neg) with
        | false =>
            rfl
        | true =>
            have hWitness :
                ∃ u ∈ m.R i w, (evalModal m u phi).neg = true := by
              simpa only [List.any_eq_true] using hAny
            rcases hWitness with ⟨u, hu, hNeg⟩
            rw [hConst u hu, hn] at hNeg
            cases hNeg
    | true =>
        cases hR : m.R i w with
        | nil =>
            exact False.elim (hNonempty hR)
        | cons first rest =>
            have hFirst : evalModal m first phi = v :=
              hConst first (by simp [hR])
            simp [hFirst, hn]
  change modalKnowledgeValue m i w (fun u => evalModal m u phi) = v
  simp [modalKnowledgeValue, hStable, hAllPos, hAnyNeg]

/-- Under local transitivity, every positive knowledge value is idempotent under
one further application of `K`:

  K+(phi)  ->  value(K K phi) = value(K phi).

The theorem preserves the complete positive knowledge value, so both `T` and
`B` are fixed by introspection. -/
theorem modal_positive_knowledge_value_idempotent_of_transitive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hKPos : (evalModal m w (ModalFormula.know i phi)).pos = true) :
    evalModal m w (ModalFormula.know i (ModalFormula.know i phi)) =
      evalModal m w (ModalFormula.know i phi) := by
  have hNonW : m.R i w ≠ [] := model_accessibility_nonempty m i w
  have hAllPos :
      (m.R i w).all (fun u => (evalModal m u phi).pos) = true := by
    have hKPos' := hKPos
    change ((m.R i w).all (fun u => (evalModal m u phi).pos) &&
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi)) = true at hKPos'
    cases hAll : (m.R i w).all (fun u => (evalModal m u phi).pos) <;>
      cases hStable : modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) <;> simp_all
  have hStable :
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) = true := by
    have hKPos' := hKPos
    change ((m.R i w).all (fun u => (evalModal m u phi).pos) &&
      modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi)) = true at hKPos'
    cases hAll : (m.R i w).all (fun u => (evalModal m u phi).pos) <;>
      cases hs : modalAccessibleValueStable (m.R i w)
        (fun u => evalModal m u phi) <;> simp_all
  cases hR : m.R i w with
  | nil =>
      exact False.elim (hNonW hR)
  | cons first rest =>
      have hFirstMem : first ∈ m.R i w := by
        simp [hR]
      have hFirstPos : (evalModal m first phi).pos = true := by
        simp only [List.all_eq_true] at hAllPos
        exact hAllPos first hFirstMem
      have hConstSource : ∀ u, u ∈ m.R i w →
          evalModal m u phi = evalModal m first phi := by
        intro u hu
        have huCases : u = first ∨ u ∈ rest := by
          simpa [hR] using hu
        rcases huCases with rfl | huRest
        · rfl
        · rw [hR] at hStable
          unfold modalAccessibleValueStable at hStable
          simp only [List.all_eq_true] at hStable
          have hEq := hStable u huRest
          simpa using hEq
      have hSourceK :
          evalModal m w (ModalFormula.know i phi) = evalModal m first phi := by
        exact modal_knowledge_recovers_nonempty_constant_profile
          m i w phi (evalModal m first phi) hNonW hConstSource
      have hEachK : ∀ u, u ∈ m.R i w →
          evalModal m u (ModalFormula.know i phi) = evalModal m first phi := by
        intro u hu
        apply modal_knowledge_recovers_nonempty_constant_profile
        · exact model_accessibility_nonempty m i u
        · intro v hv
          exact hConstSource v (hTrans u hu v hv)
      have hOuterK :
          evalModal m w (ModalFormula.know i (ModalFormula.know i phi)) =
            evalModal m first phi := by
        exact modal_knowledge_recovers_nonempty_constant_profile
          m i w (ModalFormula.know i phi) (evalModal m first phi)
          hNonW hEachK
      rw [hOuterK, hSourceK]

/-- Positive axiom 4 follows immediately from complete-value idempotence under
transitivity. -/
theorem modal_positive_introspection_of_transitive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrans : ModalTransitiveAt m i w)
    (hKPos : (evalModal m w (ModalFormula.know i phi)).pos = true) :
    (evalModal m w
      (ModalFormula.know i (ModalFormula.know i phi))).pos = true := by
  have hEq := modal_positive_knowledge_value_idempotent_of_transitive
    m i w phi hTrans hKPos
  rw [hEq]
  exact hKPos

/-- The previously verified unrestricted-introspection countermodel fails the
new recovery condition exactly where expected: its root relation is not
transitive. -/
theorem introspection_countermodel_not_transitive_at_root :
    ¬ ModalTransitiveAt IntrospectionModel IntrospectionAgent.a
      IntrospectionWorld.root := by
  intro hTrans
  have hBad :
      IntrospectionWorld.left ∈
        IntrospectionModel.R IntrospectionAgent.a IntrospectionWorld.root := by
    exact hTrans IntrospectionWorld.middle (by native_decide)
      IntrospectionWorld.left (by native_decide)
  simp [IntrospectionModel, introspectionR] at hBad

/-!
## Interpretation

Ordinary transitivity is sufficient for positive introspection in the present
4-PEL model class.  The reason is slightly richer than in ordinary Kripke
semantics:

* positive `K phi` makes the complete `phi` value homogeneous over `R(w)`;
* transitivity keeps every successor's evidence inside that homogeneous region;
* probability normalization makes each successor neighborhood nonempty;
* hence every successor recovers the same complete `K phi` value, including the
  glutty `B` case;
* the outer `K` therefore preserves that value exactly.

Thus, on transitive frames, the positive knowledge values `T` and `B` are
one-step fixed points of introspection.  The earlier countermodel fails because
its two-step successors escape the source neighborhood.

The next modal-law gate should turn to negative introspection and Euclidean
frame conditions, where the distinction between internal `not K phi`, negative
support for `K phi`, and meta-level lack of positive knowledge becomes central.
-/

end PEL4
