import PEL4.RecoveryScopeStuttering

namespace PEL4

/-!
# Gate 23: recursive causal descent for recovery changes

Gate 22 showed that a changed belief result either spends a strict unit of its
own cumulative evidence scope or inherits a changed body value from an
accessible world.  This gate follows the inherited-change branch through the
finite modal syntax tree.  Since conditionalization leaves atomic valuations
fixed, the descent must terminate at a reachable belief node whose own scope
shrinks strictly.
-/

/-- Accessible-value stability depends only on values at members of the finite
range. -/
theorem modalAccessibleValueStable_congr_on_mem
    {W : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (vAfter vBefore : W -> FDEValue)
    (hValues : ∀ u, u ∈ worlds -> vAfter u = vBefore u) :
    modalAccessibleValueStable worlds vAfter =
      modalAccessibleValueStable worlds vBefore := by
  cases worlds with
  | nil => rfl
  | cons first rest =>
      unfold modalAccessibleValueStable
      apply list_all_congr_on_mem
      intro u hu
      have hFirst : vAfter first = vBefore first :=
        hValues first (by simp)
      have hU : vAfter u = vBefore u :=
        hValues u (by simp [hu])
      rw [hU, hFirst]

/-- Knowledge values agree when the two models have the same accessible range
and their interpreted bodies agree throughout that range. -/
theorem modalKnowledgeValue_congr_on_accessible
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom)
    (i : Ag) (w : W)
    (vN vM : W -> FDEValue)
    (hR : n.R i w = m.R i w)
    (hValues : ∀ u, u ∈ m.R i w -> vN u = vM u) :
    modalKnowledgeValue n i w vN = modalKnowledgeValue m i w vM := by
  have hStable :
      modalAccessibleValueStable (m.R i w) vN =
        modalAccessibleValueStable (m.R i w) vM :=
    modalAccessibleValueStable_congr_on_mem (m.R i w) vN vM hValues
  have hAllPos :
      (m.R i w).all (fun u => (vN u).pos) =
        (m.R i w).all (fun u => (vM u).pos) := by
    apply list_all_congr_on_mem
    intro u hu
    rw [hValues u hu]
  have hAnyNeg :
      (m.R i w).any (fun u => (vN u).neg) =
        (m.R i w).any (fun u => (vM u).neg) := by
    apply list_any_congr_on_mem
    intro u hu
    rw [hValues u hu]
  unfold modalKnowledgeValue
  rw [hR]
  rw [hStable, hAllPos, hAnyNeg]

/-- Raw possibility has the analogous accessible-profile congruence. -/
theorem modalRawPossibilityValue_congr_on_accessible
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom)
    (i : Ag) (w : W)
    (vN vM : W -> FDEValue)
    (hR : n.R i w = m.R i w)
    (hValues : ∀ u, u ∈ m.R i w -> vN u = vM u) :
    modalRawPossibilityValue n i w vN =
      modalRawPossibilityValue m i w vM := by
  have hAnyPos :
      (m.R i w).any (fun u => (vN u).pos) =
        (m.R i w).any (fun u => (vM u).pos) := by
    apply list_any_congr_on_mem
    intro u hu
    rw [hValues u hu]
  have hAllNeg :
      (m.R i w).all (fun u => (vN u).neg) =
        (m.R i w).all (fun u => (vM u).neg) := by
    apply list_all_congr_on_mem
    intro u hu
    rw [hValues u hu]
  unfold modalRawPossibilityValue
  rw [hR]
  rw [hAnyPos, hAllNeg]

/-- Main Gate-23 causal-descent theorem. Any changed modal value under one
conditionalization has a reachable belief observation whose cumulative scope
shrinks strictly. The returned site belongs to the same finite compiler used
by Gate 21. -/
theorem evalModal_change_has_strictShrink_beliefObservation
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m i w (scope i w))
    (phi : ModalFormula Atom Ag) :
    ∀ w,
      evalModal (conditionalize m E hAdm) w phi ≠ evalModal m w phi ->
      ∃ site i body,
        site ∈ recoveryObservationSites m w phi ∧
        site.formula = ModalFormula.bel i body ∧
        (intersectWorlds (scope i site.world)
          (conditionalizationEvidenceEvent m i site.world E)).length <
            (scope i site.world).length := by
  induction phi with
  | prop p =>
      intro w hChange
      exact (hChange rfl).elim
  | not body ih =>
      intro w hChange
      have hBodyChange :
          evalModal (conditionalize m E hAdm) w body ≠
            evalModal m w body := by
        intro hEq
        apply hChange
        simp only [evalModal]
        rw [hEq]
      exact ih w hBodyChange
  | and left right ihLeft ihRight =>
      intro w hChange
      by_cases hLeft :
          evalModal (conditionalize m E hAdm) w left ≠
            evalModal m w left
      · obtain ⟨site, i, body, hSite, hFormula, hStrict⟩ :=
          ihLeft w hLeft
        exact ⟨site, i, body, List.mem_append_left _ hSite,
          hFormula, hStrict⟩
      · have hLeftEq :
            evalModal (conditionalize m E hAdm) w left =
              evalModal m w left := Classical.not_not.mp hLeft
        have hRight :
            evalModal (conditionalize m E hAdm) w right ≠
              evalModal m w right := by
          intro hRightEq
          apply hChange
          simp only [evalModal]
          rw [hLeftEq, hRightEq]
        obtain ⟨site, i, body, hSite, hFormula, hStrict⟩ :=
          ihRight w hRight
        exact ⟨site, i, body, List.mem_append_right _ hSite,
          hFormula, hStrict⟩
  | bel i body ih =>
      intro w hChange
      by_cases hStrict :
          (intersectWorlds (scope i w)
            (conditionalizationEvidenceEvent m i w E)).length <
              (scope i w).length
      · exact ⟨{ world := w, formula := .bel i body }, i, body,
          List.mem_cons_self, rfl, hStrict⟩
      · have hBodyChange :
            ∃ u, u ∈ m.R i w ∧
              evalModal (conditionalize m E hAdm) u body ≠
                evalModal m u body := by
          apply Classical.byContradiction
          intro hNoChange
          have hValues : ∀ u, u ∈ m.R i w ->
              evalModal (conditionalize m E hAdm) u body =
                evalModal m u body := by
            intro u hu
            apply Classical.byContradiction
            intro hNe
            apply hNoChange
            exact ⟨u, hu, hNe⟩
          have hBeliefEq :=
            belief_conditionalize_eq_of_concentrated_not_strictShrink
              m hIntegrity E hAdm i w (scope i w)
              (hConcentrated i w) hStrict
              (fun u => evalModal (conditionalize m E hAdm) u body)
              (fun u => evalModal m u body) hValues
          apply hChange
          simpa only [evalModal] using hBeliefEq
        obtain ⟨u, hu, hBodyValueChange⟩ := hBodyChange
        obtain ⟨site, j, nestedBody, hSite, hFormula, hNestedStrict⟩ :=
          ih u hBodyValueChange
        exact ⟨site, j, nestedBody,
          List.mem_cons_of_mem _
            (List.mem_flatMap.mpr ⟨u, hu, hSite⟩),
          hFormula, hNestedStrict⟩
  | know i body ih =>
      intro w hChange
      have hBodyChange :
          ∃ u, u ∈ m.R i w ∧
            evalModal (conditionalize m E hAdm) u body ≠
              evalModal m u body := by
        apply Classical.byContradiction
        intro hNoChange
        have hValues : ∀ u, u ∈ m.R i w ->
            evalModal (conditionalize m E hAdm) u body =
              evalModal m u body := by
          intro u hu
          apply Classical.byContradiction
          intro hNe
          apply hNoChange
          exact ⟨u, hu, hNe⟩
        have hKnowledgeEq := modalKnowledgeValue_congr_on_accessible
          m (conditionalize m E hAdm) i w
          (fun u => evalModal (conditionalize m E hAdm) u body)
          (fun u => evalModal m u body) rfl hValues
        apply hChange
        simpa only [evalModal] using hKnowledgeEq
      obtain ⟨u, hu, hBodyValueChange⟩ := hBodyChange
      obtain ⟨site, j, nestedBody, hSite, hFormula, hStrict⟩ :=
        ih u hBodyValueChange
      exact ⟨site, j, nestedBody,
        List.mem_flatMap.mpr ⟨u, hu, hSite⟩, hFormula, hStrict⟩
  | poss i body ih =>
      intro w hChange
      have hBodyChange :
          ∃ u, u ∈ m.R i w ∧
            evalModal (conditionalize m E hAdm) u body ≠
              evalModal m u body := by
        apply Classical.byContradiction
        intro hNoChange
        have hValues : ∀ u, u ∈ m.R i w ->
            evalModal (conditionalize m E hAdm) u body =
              evalModal m u body := by
          intro u hu
          apply Classical.byContradiction
          intro hNe
          apply hNoChange
          exact ⟨u, hu, hNe⟩
        have hPossibilityEq := modalRawPossibilityValue_congr_on_accessible
          m (conditionalize m E hAdm) i w
          (fun u => evalModal (conditionalize m E hAdm) u body)
          (fun u => evalModal m u body) rfl hValues
        apply hChange
        simpa only [evalModal] using hPossibilityEq
      obtain ⟨u, hu, hBodyValueChange⟩ := hBodyChange
      obtain ⟨site, j, nestedBody, hSite, hFormula, hStrict⟩ :=
        ih u hBodyValueChange
      exact ⟨site, j, nestedBody,
        List.mem_flatMap.mpr ⟨u, hu, hSite⟩, hFormula, hStrict⟩

/-- The Gate-21 compiler is closed under recompiling any observation that it
already contains. This lets a causal witness found below a changed compiled
site be returned to the original root compiler. -/
theorem recoveryObservationSites_closed_under_descendants
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    ∀ w site,
      site ∈ recoveryObservationSites m w phi ->
      ∀ descendant,
        descendant ∈
          recoveryObservationSites m site.world site.formula ->
        descendant ∈ recoveryObservationSites m w phi := by
  induction phi with
  | prop p =>
      intro w site hSite descendant hDescendant
      simp only [recoveryObservationSites, List.mem_singleton] at hSite
      subst site
      exact hDescendant
  | not body ih =>
      intro w site hSite descendant hDescendant
      exact ih w site hSite descendant hDescendant
  | and left right ihLeft ihRight =>
      intro w site hSite descendant hDescendant
      rcases List.mem_append.mp hSite with hLeft | hRight
      · exact List.mem_append_left _
          (ihLeft w site hLeft descendant hDescendant)
      · exact List.mem_append_right _
          (ihRight w site hRight descendant hDescendant)
  | bel i body ih =>
      intro w site hSite descendant hDescendant
      rcases List.mem_cons.mp hSite with hRoot | hNested
      · subst site
        exact hDescendant
      · obtain ⟨u, hu, hSiteInBody⟩ := List.mem_flatMap.mp hNested
        apply List.mem_cons_of_mem
        apply List.mem_flatMap.mpr
        exact ⟨u, hu,
          ih u site hSiteInBody descendant hDescendant⟩
  | know i body ih =>
      intro w site hSite descendant hDescendant
      obtain ⟨u, hu, hSiteInBody⟩ := List.mem_flatMap.mp hSite
      apply List.mem_flatMap.mpr
      exact ⟨u, hu,
        ih u site hSiteInBody descendant hDescendant⟩
  | poss i body ih =>
      intro w site hSite descendant hDescendant
      obtain ⟨u, hu, hSiteInBody⟩ := List.mem_flatMap.mp hSite
      apply List.mem_flatMap.mpr
      exact ⟨u, hu,
        ih u site hSiteInBody descendant hDescendant⟩

/-- Finite-root causal localization. Every change of compositional recovery
under conditionalization has a belief observation in the original Gate-21
compiler whose cumulative evidence scope shrinks strictly. This eliminates
Gate 22's inherited-body-change disjunct by finite recursive descent. -/
theorem recoveryOn_change_has_strictShrink_beliefObservation
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
      (intersectWorlds (scope i site.world)
        (conditionalizationEvidenceEvent m i site.world E)).length <
          (scope i site.world).length := by
  obtain ⟨changedSite, hChangedSite, hClassicalityChange⟩ :=
    recoveryOn_change_has_observation_change
      m hIntegrity E hAdm roots phi hRecoveryChange
  have hValueChange :
      evalModal (conditionalize m E hAdm)
          changedSite.world changedSite.formula ≠
        evalModal m changedSite.world changedSite.formula := by
    intro hEq
    apply hClassicalityChange
    unfold RecoveryObservationSite.IsClassicalIn
    exact Iff.of_eq (congrArg IsClassicalValue hEq.symm)
  obtain ⟨strictSite, i, body, hStrictDescendant, hFormula, hStrict⟩ :=
    evalModal_change_has_strictShrink_beliefObservation
      m hIntegrity E hAdm scope hConcentrated
      changedSite.formula changedSite.world hValueChange
  obtain ⟨root, hRoot, hChangedBelowRoot⟩ :=
    List.mem_flatMap.mp hChangedSite
  have hStrictBelowRoot :
      strictSite ∈ recoveryObservationSites m root phi :=
    recoveryObservationSites_closed_under_descendants
      m phi root changedSite hChangedBelowRoot strictSite hStrictDescendant
  exact ⟨strictSite, i, body,
    List.mem_flatMap.mpr ⟨root, hRoot, hStrictBelowRoot⟩,
    hFormula, hStrict⟩

/-- With explicit finite coverage of the ambient world type, the same strict
shrink witness exists for a change of globally quantified recovery. -/
theorem globalRecovery_change_has_strictShrink_beliefObservation_of_covers
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (hCovers : WorldListCovers roots)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m i w (scope i w))
    (hRecoveryChange : ¬
      (ModalFormula.CompositionalRecovery m phi ↔
        ModalFormula.CompositionalRecovery
          (conditionalize m E hAdm) phi)) :
    ∃ site i body,
      site ∈ recoveryObservationSitesFrom m roots phi ∧
      site.formula = ModalFormula.bel i body ∧
      (intersectWorlds (scope i site.world)
        (conditionalizationEvidenceEvent m i site.world E)).length <
          (scope i site.world).length := by
  apply recoveryOn_change_has_strictShrink_beliefObservation
    m hIntegrity E hAdm roots phi scope hConcentrated
  intro hOn
  apply hRecoveryChange
  constructor
  · intro hBefore
    have hBeforeOn :=
      (compositionalRecoveryOn_iff_global_of_covers
        m roots phi hCovers).2 hBefore
    have hAfterOn := hOn.1 hBeforeOn
    exact (compositionalRecoveryOn_iff_global_of_covers
      (conditionalize m E hAdm) roots phi hCovers).1 hAfterOn
  · intro hAfter
    have hAfterOn :=
      (compositionalRecoveryOn_iff_global_of_covers
        (conditionalize m E hAdm) roots phi hCovers).2 hAfter
    have hBeforeOn := hOn.2 hAfterOn
    exact (compositionalRecoveryOn_iff_global_of_covers
      m roots phi hCovers).1 hBeforeOn

/-- Trace-indexed Gate-23 theorem. For the next edge after any finite update
prefix, every recovery change consumes a strict Gate-20 scope loss at some
belief observation reachable in the Gate-21 compiler. -/
theorem FiniteConditionalizationTrace.finalModel_recoveryOn_change_has_strictShrink_beliefObservation
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
      (intersectWorlds
          (tracePrefix.evidenceScopeDescent i site.world).finalScope
          (conditionalizationEvidenceEvent
            tracePrefix.finalModel.toModel i site.world E)).length <
        (tracePrefix.evidenceScopeDescent i site.world).finalScope.length := by
  apply recoveryOn_change_has_strictShrink_beliefObservation
    tracePrefix.finalModel.toModel
      tracePrefix.finalModel.probability_integrity E hAdm roots phi
      (fun i w => (tracePrefix.evidenceScopeDescent i w).finalScope)
  · intro i w
    exact tracePrefix.finalModel_concentratedOn_finalScope i w
  · exact hRecoveryChange

/-! ## Gate-19 loss instance -/

/-- The first loss in the concrete Gate-19 `T -> N -> T` trace is covered by
the general causal-descent theorem: one of the twenty Gate-21 observations is
a belief node whose initial cumulative scope shrinks strictly under evidence
`q`. -/
theorem gate23_gate19_first_loss_has_strictShrink_beliefObservation :
    ∃ site i body,
      site ∈ recoveryObservationSitesFrom gate19StrongModel.toModel
        gate19Support gate19BelP ∧
      site.formula = ModalFormula.bel i body ∧
      (intersectWorlds (gate19StrongModel.toModel.R i site.world)
        (conditionalizationEvidenceEvent gate19StrongModel.toModel
          i site.world gate19EvidenceQ)).length <
        (gate19StrongModel.toModel.R i site.world).length := by
  apply globalRecovery_change_has_strictShrink_beliefObservation_of_covers
    gate19StrongModel.toModel gate19StrongModel.probability_integrity
      gate19EvidenceQ gate19EvidenceQ_admissible gate19Support
      gate21_gate19Support_covers gate19BelP
      (fun i w => gate19StrongModel.toModel.R i w)
  · intro i w
    exact localMeasureConcentratedOn_accessibility
      gate19StrongModel.toModel gate19StrongModel.probability_integrity i w
  · intro hRecoveryIff
    apply gate19_belP_not_recovered_after_first_update
    change ModalFormula.CompositionalRecovery
      (conditionalize gate19StrongModel.toModel gate19EvidenceQ
        gate19EvidenceQ_admissible) gate19BelP
    exact hRecoveryIff.1 gate19_belP_recovered_initially

end PEL4
