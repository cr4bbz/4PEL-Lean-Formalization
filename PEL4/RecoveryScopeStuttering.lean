import PEL4.FiniteReachableRecovery
import PEL4.IndependentClassicalModalSemantics

namespace PEL4

/-!
# Gate 22: cumulative-scope stuttering for belief and recovery

Gate 21 localized every recovery change to a changed belief-result
observation. Gate 22 asks whether such a change must spend a new unit of the
cumulative evidence scope bounded in Gate 20.

The missing invariant is probabilistic rather than merely list-theoretic: the
current posterior measure must be concentrated on the cumulative scope left by
the preceding updates. This file establishes that invariant and uses it to
prove that an update which removes no further cumulative-scope world is
locally measure-stuttering.
-/

/-- If every member of `A` lies in `B`, filtering `A` by membership in `B`
returns `A` exactly, including its order. -/
theorem intersectWorlds_eq_left_of_subset
    {W : Type} [DecidableEq W]
    (A B : FiniteSet W)
    (hAB : FiniteEventSubset A B) :
    intersectWorlds A B = A := by
  unfold intersectWorlds
  rw [List.filter_eq_self]
  intro x hx
  exact List.contains_iff_mem.mpr (hAB x hx)

/-- If intersection does not shorten a finite scope, every scope member lies
in the intersecting evidence event. -/
theorem subset_of_intersectWorlds_not_length_lt
    {W : Type} [DecidableEq W]
    (scope evidence : FiniteSet W)
    (hNotStrict : ¬ (intersectWorlds scope evidence).length < scope.length) :
    FiniteEventSubset scope evidence := by
  have hEq : (intersectWorlds scope evidence).length = scope.length := by
    apply Nat.le_antisymm
    · exact FiniteEvidenceScopeDescent.intersectWorlds_length_le scope evidence
    · exact Nat.le_of_not_gt hNotStrict
  have hAll := (List.length_filter_eq_length_iff.mp hEq)
  intro x hx
  exact List.contains_iff_mem.mp (hAll x hx)

/-- A local finite measure is concentrated on `scope` when every well-formed
accessible event has exactly the mass of its intersection with `scope`. -/
structure LocalMeasureConcentratedOn
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag) (w : W)
    (scope : FiniteSet W) : Prop where
  scope_nodup : scope.Nodup
  scope_subset : FiniteEventSubset scope (m.R i w)
  restricts :
    ∀ S : FiniteSet W,
      S.Nodup ->
      FiniteEventSubset S (m.R i w) ->
      m.mu i w S = m.mu i w (intersectWorlds S scope)

/-- Before any updates, a probability-integrity measure is concentrated on
its full accessibility scope. -/
theorem localMeasureConcentratedOn_accessibility
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W) :
    LocalMeasureConcentratedOn m i w (m.R i w) := by
  refine
    { scope_nodup := (hIntegrity i w).support_nodup
      scope_subset := fun _ hx => hx
      restricts := ?_ }
  intro S hSNodup hSSub
  rw [intersectWorlds_eq_left_of_subset S (m.R i w) hSSub]

/-- Concentration descends through conditionalization to the intersection of
the old scope with the new positive-evidence event. -/
theorem conditionalize_preserves_localMeasureConcentration
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    (scope : FiniteSet W)
    (hConcentrated : LocalMeasureConcentratedOn m i w scope) :
    LocalMeasureConcentratedOn (conditionalize m E hAdm) i w
      (intersectWorlds scope
        (conditionalizationEvidenceEvent m i w E)) := by
  let evidence := conditionalizationEvidenceEvent m i w E
  let nextScope := intersectWorlds scope evidence
  have hEvidenceNodup : evidence.Nodup :=
    conditionalizationEvidenceEvent_nodup m hIntegrity i w E
  have hEvidenceSub : FiniteEventSubset evidence (m.R i w) :=
    conditionalizationEvidenceEvent_subset m i w E
  have hDenNe : m.mu i w evidence ≠ 0 := by
    simpa [conditionalizationEvidenceMass,
      conditionalizationEvidenceEvent, evidence] using
      hAdm.positive_mass i w
  have hDenNeRaw :
      m.mu i w
        (filterWorlds (m.R i w) (fun u => (eval m u E).pos)) ≠ 0 := by
    simpa [evidence, conditionalizationEvidenceEvent] using hDenNe
  refine
    { scope_nodup := intersectWorlds_nodup scope evidence
        hConcentrated.scope_nodup
      scope_subset := ?_
      restricts := ?_ }
  · intro x hx
    exact hConcentrated.scope_subset x
      (intersectWorlds_subset_left scope evidence x hx)
  · intro S hSNodup hSSub
    change conditionalize_mu m i w E S =
      conditionalize_mu m i w E (intersectWorlds S nextScope)
    simp only [conditionalize_mu, beq_iff_eq]
    rw [if_neg hDenNeRaw]
    rw [if_neg hDenNeRaw]
    apply congrArg (fun q : Rat => q / m.mu i w evidence)
    let A := intersectWorlds S evidence
    let C := intersectWorlds A scope
    let B := intersectWorlds (intersectWorlds S nextScope) evidence
    have hANodup : A.Nodup :=
      intersectWorlds_nodup S evidence hSNodup
    have hASub : FiniteEventSubset A (m.R i w) := by
      intro x hx
      exact hEvidenceSub x (intersectWorlds_subset_right S evidence x hx)
    have hRestrictA : m.mu i w A = m.mu i w C :=
      hConcentrated.restricts A hANodup hASub
    have hCNodup : C.Nodup :=
      intersectWorlds_nodup A scope hANodup
    have hCSub : FiniteEventSubset C (m.R i w) := by
      intro x hx
      exact hConcentrated.scope_subset x
        (intersectWorlds_subset_right A scope x hx)
    have hInterSNodup : (intersectWorlds S nextScope).Nodup :=
      intersectWorlds_nodup S nextScope hSNodup
    have hBNodup : B.Nodup :=
      intersectWorlds_nodup (intersectWorlds S nextScope) evidence
        hInterSNodup
    have hBSub : FiniteEventSubset B (m.R i w) := by
      intro x hx
      exact hEvidenceSub x
        (intersectWorlds_subset_right (intersectWorlds S nextScope)
          evidence x hx)
    have hCBExt : FiniteEventExtEq C B := by
      intro x
      simp [C, B, A, nextScope, intersectWorlds, and_left_comm]
    calc
      m.mu i w (intersectWorlds S evidence) = m.mu i w C := hRestrictA
      _ = m.mu i w B :=
        (hIntegrity i w).extensional C B hCNodup hBNodup hCSub hBSub hCBExt
      _ = m.mu i w
          (intersectWorlds (intersectWorlds S nextScope) evidence) := rfl

/-- If the next evidence event contains the whole current concentration scope,
conditionalization leaves the local measure unchanged on every well-formed
accessible event. -/
theorem conditionalize_mu_eq_of_concentrated_scope_subset_evidence
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    (scope : FiniteSet W)
    (hConcentrated : LocalMeasureConcentratedOn m i w scope)
    (hScopeEvidence : FiniteEventSubset scope
      (conditionalizationEvidenceEvent m i w E))
    (S : FiniteSet W)
    (hSNodup : S.Nodup)
    (hSSub : FiniteEventSubset S (m.R i w)) :
    conditionalize_mu m i w E S = m.mu i w S := by
  let evidence := conditionalizationEvidenceEvent m i w E
  have hEvidenceNodup : evidence.Nodup :=
    conditionalizationEvidenceEvent_nodup m hIntegrity i w E
  have hEvidenceSub : FiniteEventSubset evidence (m.R i w) :=
    conditionalizationEvidenceEvent_subset m i w E
  have hDenNe : m.mu i w evidence ≠ 0 := by
    simpa [conditionalizationEvidenceMass,
      conditionalizationEvidenceEvent, evidence] using
      hAdm.positive_mass i w
  have hDenNeRaw :
      m.mu i w
        (filterWorlds (m.R i w) (fun u => (eval m u E).pos)) ≠ 0 := by
    simpa [evidence, conditionalizationEvidenceEvent] using hDenNe
  have hScopeMass : m.mu i w scope = 1 := by
    have hRRestrict := hConcentrated.restricts
      (m.R i w) (hIntegrity i w).support_nodup (fun _ hx => hx)
    have hInterNodup := intersectWorlds_nodup
      (m.R i w) scope (hIntegrity i w).support_nodup
    have hInterSub := intersectWorlds_subset_left (m.R i w) scope
    have hExt : FiniteEventExtEq (intersectWorlds (m.R i w) scope) scope :=
      intersectWorlds_left_extensional_right
        (m.R i w) scope hConcentrated.scope_subset
    have hInterEq := (hIntegrity i w).extensional
      (intersectWorlds (m.R i w) scope) scope
      hInterNodup hConcentrated.scope_nodup hInterSub
      hConcentrated.scope_subset hExt
    calc
      m.mu i w scope = m.mu i w (intersectWorlds (m.R i w) scope) := hInterEq.symm
      _ = m.mu i w (m.R i w) := hRRestrict.symm
      _ = 1 := (hIntegrity i w).total
  have hEvidenceMass : m.mu i w evidence = 1 := by
    have hRestrict := hConcentrated.restricts evidence
      hEvidenceNodup hEvidenceSub
    have hInterNodup := intersectWorlds_nodup evidence scope hEvidenceNodup
    have hInterSub : FiniteEventSubset
        (intersectWorlds evidence scope) (m.R i w) := by
      intro x hx
      exact hEvidenceSub x
        (intersectWorlds_subset_left evidence scope x hx)
    have hExt : FiniteEventExtEq (intersectWorlds evidence scope) scope := by
      intro x
      constructor
      · exact intersectWorlds_subset_right evidence scope x
      · intro hx
        exact List.mem_filter.mpr
          ⟨hScopeEvidence x hx, List.contains_iff_mem.mpr hx⟩
    have hInterEq := (hIntegrity i w).extensional
      (intersectWorlds evidence scope) scope
      hInterNodup hConcentrated.scope_nodup hInterSub
      hConcentrated.scope_subset hExt
    calc
      m.mu i w evidence = m.mu i w (intersectWorlds evidence scope) := hRestrict
      _ = m.mu i w scope := hInterEq
      _ = 1 := hScopeMass
  have hNumerator : m.mu i w (intersectWorlds S evidence) = m.mu i w S := by
    let A := intersectWorlds S evidence
    let C := intersectWorlds A scope
    let D := intersectWorlds S scope
    have hANodup : A.Nodup := intersectWorlds_nodup S evidence hSNodup
    have hASub : FiniteEventSubset A (m.R i w) := by
      intro x hx
      exact hEvidenceSub x (intersectWorlds_subset_right S evidence x hx)
    have hCNodup : C.Nodup := intersectWorlds_nodup A scope hANodup
    have hDNodup : D.Nodup := intersectWorlds_nodup S scope hSNodup
    have hCSub : FiniteEventSubset C (m.R i w) := by
      intro x hx
      exact hConcentrated.scope_subset x
        (intersectWorlds_subset_right A scope x hx)
    have hDSub : FiniteEventSubset D (m.R i w) := by
      intro x hx
      exact hConcentrated.scope_subset x
        (intersectWorlds_subset_right S scope x hx)
    have hCDExt : FiniteEventExtEq C D := by
      intro x
      constructor
      · intro hx
        have hxA : x ∈ A := intersectWorlds_subset_left A scope x hx
        have hxS : x ∈ S := intersectWorlds_subset_left S evidence x hxA
        have hxScope : x ∈ scope :=
          intersectWorlds_subset_right A scope x hx
        exact List.mem_filter.mpr
          ⟨hxS, List.contains_iff_mem.mpr hxScope⟩
      · intro hx
        have hxS : x ∈ S := intersectWorlds_subset_left S scope x hx
        have hxScope : x ∈ scope :=
          intersectWorlds_subset_right S scope x hx
        have hxEvidence : x ∈ evidence := hScopeEvidence x hxScope
        have hxA : x ∈ A := List.mem_filter.mpr
          ⟨hxS, List.contains_iff_mem.mpr hxEvidence⟩
        exact List.mem_filter.mpr
          ⟨hxA, List.contains_iff_mem.mpr hxScope⟩
    have hCDEq := (hIntegrity i w).extensional
      C D hCNodup hDNodup hCSub hDSub hCDExt
    calc
      m.mu i w (intersectWorlds S evidence) = m.mu i w C :=
        hConcentrated.restricts A hANodup hASub
      _ = m.mu i w D := hCDEq
      _ = m.mu i w S :=
        (hConcentrated.restricts S hSNodup hSSub).symm
  simp only [conditionalize_mu, beq_iff_eq]
  rw [if_neg hDenNeRaw]
  change m.mu i w (intersectWorlds S evidence) / m.mu i w evidence =
    m.mu i w S
  rw [hNumerator, hEvidenceMass]
  rw [Rat.div_def]
  have hInvOne : (1 : Rat)⁻¹ = 1 := by
    simpa only [Rat.one_mul] using
      (Rat.mul_inv_cancel (1 : Rat) (by decide : (1 : Rat) ≠ 0))
  rw [hInvOne, Rat.mul_one]

/-- The Gate-20 non-strict length test supplies the scope-in-evidence premise
for local measure stuttering. -/
theorem conditionalize_mu_eq_of_concentrated_not_strictShrink
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    (scope : FiniteSet W)
    (hConcentrated : LocalMeasureConcentratedOn m i w scope)
    (hNotStrict : ¬
      (intersectWorlds scope
        (conditionalizationEvidenceEvent m i w E)).length < scope.length)
    (S : FiniteSet W)
    (hSNodup : S.Nodup)
    (hSSub : FiniteEventSubset S (m.R i w)) :
    conditionalize_mu m i w E S = m.mu i w S := by
  exact conditionalize_mu_eq_of_concentrated_scope_subset_evidence
    m hIntegrity E hAdm i w scope hConcentrated
    (subset_of_intersectWorlds_not_length_lt scope
      (conditionalizationEvidenceEvent m i w E) hNotStrict)
    S hSNodup hSSub

/-- If the interpreted body values agree throughout the accessible range and
the update spends no new cumulative-scope world, the complete four-valued
belief result stutters.  Both its positive and negative threshold bits are
preserved. -/
theorem belief_conditionalize_eq_of_concentrated_not_strictShrink
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    (scope : FiniteSet W)
    (hConcentrated : LocalMeasureConcentratedOn m i w scope)
    (hNotStrict : ¬
      (intersectWorlds scope
        (conditionalizationEvidenceEvent m i w E)).length < scope.length)
    (vAfter vBefore : W -> FDEValue)
    (hValues : ∀ u, u ∈ m.R i w -> vAfter u = vBefore u) :
    belief (conditionalize m E hAdm) i w vAfter =
      belief m i w vBefore := by
  have hPosEvents :
      filterWorlds (m.R i w) (fun u => (vAfter u).pos) =
        filterWorlds (m.R i w) (fun u => (vBefore u).pos) := by
    unfold filterWorlds
    apply list_filter_congr_on_mem
    intro u hu
    rw [hValues u hu]
  have hNegEvents :
      filterWorlds (m.R i w) (fun u => (vAfter u).neg) =
        filterWorlds (m.R i w) (fun u => (vBefore u).neg) := by
    unfold filterWorlds
    apply list_filter_congr_on_mem
    intro u hu
    rw [hValues u hu]
  let posEvent := filterWorlds (m.R i w) (fun u => (vBefore u).pos)
  let negEvent := filterWorlds (m.R i w) (fun u => (vBefore u).neg)
  have hPosNodup : posEvent.Nodup :=
    filterWorlds_nodup (m.R i w) _ (hIntegrity i w).support_nodup
  have hNegNodup : negEvent.Nodup :=
    filterWorlds_nodup (m.R i w) _ (hIntegrity i w).support_nodup
  have hPosSub : FiniteEventSubset posEvent (m.R i w) := by
    intro u hu
    exact (List.mem_filter.mp hu).1
  have hNegSub : FiniteEventSubset negEvent (m.R i w) := by
    intro u hu
    exact (List.mem_filter.mp hu).1
  have hPosMass := conditionalize_mu_eq_of_concentrated_not_strictShrink
    m hIntegrity E hAdm i w scope hConcentrated hNotStrict
      posEvent hPosNodup hPosSub
  have hNegMass := conditionalize_mu_eq_of_concentrated_not_strictShrink
    m hIntegrity E hAdm i w scope hConcentrated hNotStrict
      negEvent hNegNodup hNegSub
  have hPosMass' : conditionalize_mu m i w E
      (filterWorlds (m.R i w) (fun u => (vBefore u).pos)) =
        m.mu i w (filterWorlds (m.R i w) (fun u => (vBefore u).pos)) := by
    simpa [posEvent] using hPosMass
  have hNegMass' : conditionalize_mu m i w E
      (filterWorlds (m.R i w) (fun u => (vBefore u).neg)) =
        m.mu i w (filterWorlds (m.R i w) (fun u => (vBefore u).neg)) := by
    simpa [negEvent] using hNegMass
  unfold belief
  simp only [conditionalize]
  simp [hPosEvents, hNegEvents, hPosMass', hNegMass']

/-- A changed classical/nonclassical status at a belief node has only two
possible sources: the update strictly removes a world from the node's current
cumulative scope, or the modal body has already changed at an accessible
world.  The second disjunct identifies the recursive dependency that a later
gate must chase through the Gate-21 observation tree. -/
theorem belief_classicality_change_implies_strictShrink_or_body_change
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (body : ModalFormula Atom Ag)
    (scope : FiniteSet W)
    (hConcentrated : LocalMeasureConcentratedOn m i w scope)
    (hClassicalityChange : ¬
      (IsClassicalValue (evalModal m w (.bel i body)) ↔
        IsClassicalValue
          (evalModal (conditionalize m E hAdm) w (.bel i body)))) :
    (intersectWorlds scope
        (conditionalizationEvidenceEvent m i w E)).length < scope.length ∨
      ∃ u, u ∈ m.R i w ∧
        evalModal (conditionalize m E hAdm) u body ≠
          evalModal m u body := by
  by_cases hStrict :
      (intersectWorlds scope
        (conditionalizationEvidenceEvent m i w E)).length < scope.length
  · exact Or.inl hStrict
  · right
    apply Classical.byContradiction
    intro hNoBodyChange
    have hValues : ∀ u, u ∈ m.R i w ->
        evalModal (conditionalize m E hAdm) u body = evalModal m u body := by
      intro u hu
      apply Classical.byContradiction
      intro hNe
      apply hNoBodyChange
      exact ⟨u, hu, hNe⟩
    have hBeliefEq :=
      belief_conditionalize_eq_of_concentrated_not_strictShrink
        m hIntegrity E hAdm i w scope hConcentrated hStrict
        (fun u => evalModal (conditionalize m E hAdm) u body)
        (fun u => evalModal m u body) hValues
    apply hClassicalityChange
    simpa only [evalModal] using
      Iff.of_eq (congrArg IsClassicalValue hBeliefEq.symm)

/-- Gate-21/Gate-22 bridge.  Every finite-root recovery change has a compiled
belief witness at which either cumulative evidence shrinks strictly, or the
change was inherited from an accessible evaluation of that belief's body. -/
theorem recoveryOn_change_has_strictShrink_or_body_change
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m i w (scope i w))
    (hRecoveryChange : ¬
      (ModalFormula.CompositionalRecoveryOn m roots phi ↔
        ModalFormula.CompositionalRecoveryOn
          (conditionalize m E hAdm) roots phi)) :
    ∃ site i body,
      site ∈ recoveryObservationSitesFrom m roots phi ∧
      site.formula = ModalFormula.bel i body ∧
      ((intersectWorlds (scope i site.world)
          (conditionalizationEvidenceEvent m i site.world E)).length <
            (scope i site.world).length ∨
        ∃ u, u ∈ m.R i site.world ∧
          evalModal (conditionalize m E hAdm) u body ≠
            evalModal m u body) := by
  obtain ⟨site, hSite, hBelief, hChange⟩ :=
    recoveryOn_change_has_belief_observation_change
      m hIntegrity E hAdm roots phi hRecoveryChange
  obtain ⟨i, body, hFormula⟩ := hBelief
  refine ⟨site, i, body, hSite, hFormula, ?_⟩
  rcases site with ⟨world, formula⟩
  dsimp at hFormula hChange ⊢
  subst formula
  exact belief_classicality_change_implies_strictShrink_or_body_change
    m hIntegrity E hAdm i world body (scope i world)
      (hConcentrated i world) hChange

/-- The posterior at the end of a dependent update trace is concentrated on
the cumulative evidence scope compiled by Gate 20.  This is the invariant
needed to interpret Gate 20's list-theoretic scope as a support envelope for
the current local probability measure. -/
theorem FiniteConditionalizationTrace.finalModel_concentratedOn_finalScopeFrom
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (i : Ag) (w : W) (scope : FiniteSet W)
    (hConcentrated : LocalMeasureConcentratedOn m.toModel i w scope) :
    LocalMeasureConcentratedOn trace.finalModel.toModel i w
      (trace.evidenceScopeDescentFrom i w scope).finalScope := by
  induction trace generalizing scope with
  | nil m =>
      exact hConcentrated
  | step m E hAdm tail ih =>
      have hNext := conditionalize_preserves_localMeasureConcentration
        m.toModel m.probability_integrity E hAdm i w scope hConcentrated
      exact ih
        (intersectWorlds scope
          (conditionalizationEvidenceEvent m.toModel i w E))
        hNext

/-- In particular, every final posterior is concentrated on the Gate-20
descent that starts from the initial accessibility list. -/
theorem FiniteConditionalizationTrace.finalModel_concentratedOn_finalScope
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (i : Ag) (w : W) :
    LocalMeasureConcentratedOn trace.finalModel.toModel i w
      (trace.evidenceScopeDescent i w).finalScope := by
  exact trace.finalModel_concentratedOn_finalScopeFrom i w (m.toModel.R i w)
    (localMeasureConcentratedOn_accessibility
      m.toModel m.probability_integrity i w)

/-- Trace-indexed form of the Gate-21/Gate-22 bridge.  At the next edge after
any finite prefix, the relevant scope is the cumulative final scope compiled
from that prefix; no separately postulated concentration invariant is
needed. -/
theorem FiniteConditionalizationTrace.finalModel_recoveryOn_change_has_strictShrink_or_body_change
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (tracePrefix : FiniteConditionalizationTrace m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible tracePrefix.finalModel.toModel E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (hRecoveryChange : ¬
      (ModalFormula.CompositionalRecoveryOn
          tracePrefix.finalModel.toModel roots phi ↔
        ModalFormula.CompositionalRecoveryOn
          (conditionalize tracePrefix.finalModel.toModel E hAdm) roots phi)) :
    ∃ site i body,
      site ∈ recoveryObservationSitesFrom
        tracePrefix.finalModel.toModel roots phi ∧
      site.formula = ModalFormula.bel i body ∧
      ((intersectWorlds
          (tracePrefix.evidenceScopeDescent i site.world).finalScope
          (conditionalizationEvidenceEvent
            tracePrefix.finalModel.toModel i site.world E)).length <
          (tracePrefix.evidenceScopeDescent i site.world).finalScope.length ∨
        ∃ u, u ∈ tracePrefix.finalModel.toModel.R i site.world ∧
          evalModal
              (conditionalize tracePrefix.finalModel.toModel E hAdm) u body ≠
            evalModal tracePrefix.finalModel.toModel u body) := by
  apply recoveryOn_change_has_strictShrink_or_body_change
    tracePrefix.finalModel.toModel tracePrefix.finalModel.probability_integrity
      E hAdm roots phi
      (fun i w => (tracePrefix.evidenceScopeDescent i w).finalScope)
  · intro i w
    exact tracePrefix.finalModel_concentratedOn_finalScope i w
  · exact hRecoveryChange

end PEL4
