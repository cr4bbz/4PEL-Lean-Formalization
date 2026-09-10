import PEL4.DirectionalThresholdRecovery
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Gate 13: probability integrity under conditionalization

Gate 12 isolated directed gap creation as the exact obstruction to preservation
of the recursive recovery certificate. Its remaining probabilistic boundary was
posterior integrity: the lightweight update interface did not itself carry all
finite-measure laws as fields.

Gate 13 proves that no new update axiom is needed. Prior
`ModelProbabilityIntegrity` and the existing positive-mass admissibility proof
are sufficient to derive nonnegativity, extensionality, monotonicity, finite
additivity, empty mass, and total mass for the quotient measure. The resulting
posterior integrity turns the Gate-12 certificate equivalence into an exact
recursive semantic classicality theorem.
-/

theorem filterWorlds_nodup
    {W : Type} (xs : FiniteSet W) (p : W → Bool)
    (h : xs.Nodup) :
    (filterWorlds xs p).Nodup := by
  induction xs with
  | nil => simp [filterWorlds]
  | cons a xs ih =>
      simp only [List.nodup_cons] at h
      cases hp : p a with
      | false =>
          simpa [filterWorlds, hp] using ih h.2
      | true =>
          have ha : a ∉ filterWorlds xs p := by
            intro ha
            exact h.1 ((List.mem_filter.mp ha).1)
          simpa [filterWorlds, hp] using List.nodup_cons.mpr ⟨ha, ih h.2⟩

theorem intersectWorlds_subset_left
    {W : Type} [DecidableEq W]
    (A B : FiniteSet W) :
    FiniteEventSubset (intersectWorlds A B) A := by
  intro x hx
  have h := (List.mem_filter.mp hx)
  exact h.1

theorem intersectWorlds_subset_right
    {W : Type} [DecidableEq W]
    (A B : FiniteSet W) :
    FiniteEventSubset (intersectWorlds A B) B := by
  intro x hx
  have h := (List.mem_filter.mp hx)
  exact List.contains_iff_mem.mp h.2

theorem intersectWorlds_nodup
    {W : Type} [DecidableEq W]
    (A B : FiniteSet W) (hA : A.Nodup) :
    (intersectWorlds A B).Nodup := by
  exact filterWorlds_nodup A (fun x => B.contains x) hA

theorem intersectWorlds_monotone_left
    {W : Type} [DecidableEq W]
    {A B : FiniteSet W} (E : FiniteSet W)
    (hAB : FiniteEventSubset A B) :
    FiniteEventSubset (intersectWorlds A E) (intersectWorlds B E) := by
  intro x hx
  simp only [intersectWorlds, List.mem_filter] at hx ⊢
  exact ⟨hAB x hx.1, hx.2⟩

theorem intersectWorlds_extensional_left
    {W : Type} [DecidableEq W]
    {A B : FiniteSet W} (E : FiniteSet W)
    (hAB : FiniteEventExtEq A B) :
    FiniteEventExtEq (intersectWorlds A E) (intersectWorlds B E) := by
  intro x
  simp only [intersectWorlds, List.mem_filter]
  exact and_congr (hAB x) Iff.rfl

theorem intersectWorlds_disjoint_left
    {W : Type} [DecidableEq W]
    {A B : FiniteSet W} (E : FiniteSet W)
    (hAB : FiniteEventDisjoint A B) :
    FiniteEventDisjoint (intersectWorlds A E) (intersectWorlds B E) := by
  intro x hxA hxB
  exact hAB x (intersectWorlds_subset_left A E x hxA)
    (intersectWorlds_subset_left B E x hxB)

theorem intersectWorlds_append
    {W : Type} [DecidableEq W]
    (A B E : FiniteSet W) :
    intersectWorlds (A ++ B) E =
      intersectWorlds A E ++ intersectWorlds B E := by
  exact List.filter_append A B

/-- If `E` is already contained in `A`, intersecting `A` with `E` is
extensionally just `E`, even though finite events are represented by lists. -/
theorem intersectWorlds_left_extensional_right
    {W : Type} [DecidableEq W]
    (A E : FiniteSet W)
    (hEA : FiniteEventSubset E A) :
    FiniteEventExtEq (intersectWorlds A E) E := by
  intro x
  constructor
  · exact intersectWorlds_subset_right A E x
  · intro hx
    exact List.mem_filter.mpr
      ⟨hEA x hx, List.contains_iff_mem.mpr hx⟩

/-- The accessible positive extension used as the conditioning event. -/
def conditionalizationEvidenceEvent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (E : Formula Atom Ag) : FiniteSet W :=
  filterWorlds (m.R i w) (fun u => (eval m u E).pos)

theorem conditionalizationEvidenceEvent_nodup
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W) (E : Formula Atom Ag) :
    (conditionalizationEvidenceEvent m i w E).Nodup := by
  exact filterWorlds_nodup _ _ (hIntegrity i w).support_nodup

theorem conditionalizationEvidenceEvent_subset
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag) (w : W) (E : Formula Atom Ag) :
    FiniteEventSubset (conditionalizationEvidenceEvent m i w E) (m.R i w) := by
  intro x hx
  exact (List.mem_filter.mp hx).1

/-- On an integrity-certified prior, the existing three-field admissibility
contract is equivalent to its scientifically substantive field: nonzero local
evidence mass. The two normalization fields are derived quotient-measure laws,
not additional assumptions. -/
theorem conditionalizationAdmissible_iff_positiveMass_of_probabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag) :
    ConditionalizationAdmissible m E ↔
      ∀ (i : Ag) (w : W), conditionalizationEvidenceMass m i w E ≠ 0 := by
  constructor
  · intro hAdm
    exact hAdm.positive_mass
  · intro hPositive
    refine
      { positive_mass := hPositive
        mu_total := ?_
        mu_empty := ?_ }
    · intro i w
      let evidence := conditionalizationEvidenceEvent m i w E
      have hEvidenceNodup : evidence.Nodup :=
        conditionalizationEvidenceEvent_nodup m hIntegrity i w E
      have hEvidenceSub : FiniteEventSubset evidence (m.R i w) :=
        conditionalizationEvidenceEvent_subset m i w E
      have hInterNodup :
          (intersectWorlds (m.R i w) evidence).Nodup :=
        intersectWorlds_nodup (m.R i w) evidence
          (hIntegrity i w).support_nodup
      have hInterSub :
          FiniteEventSubset (intersectWorlds (m.R i w) evidence)
            (m.R i w) :=
        intersectWorlds_subset_left (m.R i w) evidence
      have hNumEq :
          m.mu i w (intersectWorlds (m.R i w) evidence) =
            m.mu i w evidence :=
        (hIntegrity i w).extensional
          (intersectWorlds (m.R i w) evidence) evidence
          hInterNodup hEvidenceNodup hInterSub hEvidenceSub
          (intersectWorlds_left_extensional_right
            (m.R i w) evidence hEvidenceSub)
      have hDenNe : m.mu i w evidence ≠ 0 := by
        simpa [conditionalizationEvidenceMass,
          conditionalizationEvidenceEvent, evidence] using hPositive i w
      have hDenNeRaw :
          m.mu i w
            (filterWorlds (m.R i w) (fun u => (eval m u E).pos)) ≠ 0 := by
        simpa [evidence, conditionalizationEvidenceEvent] using hDenNe
      simp only [conditionalize_mu]
      simp only [beq_iff_eq]
      rw [if_neg hDenNeRaw]
      change
        m.mu i w (intersectWorlds (m.R i w) evidence) /
          m.mu i w evidence = 1
      rw [hNumEq, Rat.div_def]
      exact Rat.mul_inv_cancel (m.mu i w evidence) hDenNe
    · intro i w
      have hDenNeRaw :
          m.mu i w
            (filterWorlds (m.R i w) (fun u => (eval m u E).pos)) ≠ 0 := by
        simpa [conditionalizationEvidenceMass] using hPositive i w
      simp only [conditionalize_mu]
      simp only [beq_iff_eq]
      rw [if_neg hDenNeRaw]
      simp [intersectWorlds, (hIntegrity i w).empty, Rat.div_def]

theorem conditionalizationEvidenceMass_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) :
    0 < m.mu i w (conditionalizationEvidenceEvent m i w E) := by
  have hNonneg := (hIntegrity i w).nonnegative
    (conditionalizationEvidenceEvent m i w E)
    (conditionalizationEvidenceEvent_nodup m hIntegrity i w E)
    (conditionalizationEvidenceEvent_subset m i w E)
  have hNe : m.mu i w (conditionalizationEvidenceEvent m i w E) ≠ 0 := by
    simpa [conditionalizationEvidenceMass, conditionalizationEvidenceEvent]
      using hAdm.positive_mass i w
  exact Rat.lt_of_le_of_ne hNonneg hNe.symm

theorem conditionalize_preserves_probabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E) :
    ModelProbabilityIntegrity (conditionalize m E hAdm) := by
  intro i w
  change FiniteProbabilityIntegrity
    (conditionalize_mu m i w E) (m.R i w)
  let evidence := conditionalizationEvidenceEvent m i w E
  have hEvidenceNodup : evidence.Nodup := by
    exact conditionalizationEvidenceEvent_nodup m hIntegrity i w E
  have hEvidenceSub : FiniteEventSubset evidence (m.R i w) := by
    exact conditionalizationEvidenceEvent_subset m i w E
  have hDenPos : 0 < m.mu i w evidence := by
    exact conditionalizationEvidenceMass_pos m hIntegrity E hAdm i w
  have hDenNe : m.mu i w evidence ≠ 0 := Rat.ne_of_gt hDenPos
  have hDenNeRaw :
      m.mu i w (filterWorlds (m.R i w) (fun u => (eval m u E).pos)) ≠ 0 := by
    simpa [evidence, conditionalizationEvidenceEvent] using hDenNe
  have hInvNonneg : 0 ≤ (m.mu i w evidence)⁻¹ :=
    Rat.le_of_lt (Rat.inv_pos.mpr hDenPos)
  refine
    { support_nodup := (hIntegrity i w).support_nodup
      nonnegative := ?_
      extensional := ?_
      monotone := ?_
      add_disjoint := ?_
      empty := hAdm.mu_empty i w
      total := hAdm.mu_total i w }
  · intro S hSNodup hSSub
    have hInterNodup := intersectWorlds_nodup S evidence hSNodup
    have hInterSub :
        FiniteEventSubset (intersectWorlds S evidence) (m.R i w) := by
      intro x hx
      exact hEvidenceSub x (intersectWorlds_subset_right S evidence x hx)
    have hNumNonneg :=
      (hIntegrity i w).nonnegative
        (intersectWorlds S evidence) hInterNodup hInterSub
    simpa [conditionalize_mu, hDenNeRaw, evidence,
      conditionalizationEvidenceEvent, Rat.div_def] using
      Rat.mul_nonneg hNumNonneg hInvNonneg
  · intro A B hANodup hBNodup hASub hBSub hExt
    have hIANodup := intersectWorlds_nodup A evidence hANodup
    have hIBNodup := intersectWorlds_nodup B evidence hBNodup
    have hIASub : FiniteEventSubset (intersectWorlds A evidence) (m.R i w) := by
      intro x hx
      exact hEvidenceSub x (intersectWorlds_subset_right A evidence x hx)
    have hIBSub : FiniteEventSubset (intersectWorlds B evidence) (m.R i w) := by
      intro x hx
      exact hEvidenceSub x (intersectWorlds_subset_right B evidence x hx)
    have hNumEq := (hIntegrity i w).extensional
      (intersectWorlds A evidence) (intersectWorlds B evidence)
      hIANodup hIBNodup hIASub hIBSub
      (intersectWorlds_extensional_left evidence hExt)
    simpa [conditionalize_mu, hDenNeRaw, evidence,
      conditionalizationEvidenceEvent] using
      congrArg (fun q : Rat => q / m.mu i w evidence) hNumEq
  · intro A B hANodup hBNodup hAB hBSub
    have hIANodup := intersectWorlds_nodup A evidence hANodup
    have hIBNodup := intersectWorlds_nodup B evidence hBNodup
    have hIBSub : FiniteEventSubset (intersectWorlds B evidence) (m.R i w) := by
      intro x hx
      exact hBSub x (intersectWorlds_subset_left B evidence x hx)
    have hNumLe := (hIntegrity i w).monotone
      (intersectWorlds A evidence) (intersectWorlds B evidence)
      hIANodup hIBNodup
      (intersectWorlds_monotone_left evidence hAB) hIBSub
    simpa [conditionalize_mu, hDenNeRaw, evidence,
      conditionalizationEvidenceEvent, Rat.div_def] using
      Rat.mul_le_mul_of_nonneg_right hNumLe hInvNonneg
  · intro A B hANodup hBNodup hASub hBSub hDisjoint
    have hIANodup := intersectWorlds_nodup A evidence hANodup
    have hIBNodup := intersectWorlds_nodup B evidence hBNodup
    have hIASub : FiniteEventSubset (intersectWorlds A evidence) (m.R i w) := by
      intro x hx
      exact hASub x (intersectWorlds_subset_left A evidence x hx)
    have hIBSub : FiniteEventSubset (intersectWorlds B evidence) (m.R i w) := by
      intro x hx
      exact hBSub x (intersectWorlds_subset_left B evidence x hx)
    have hNumAdd := (hIntegrity i w).add_disjoint
      (intersectWorlds A evidence) (intersectWorlds B evidence)
      hIANodup hIBNodup hIASub hIBSub
      (intersectWorlds_disjoint_left evidence hDisjoint)
    simpa [conditionalize_mu, hDenNeRaw, evidence,
      conditionalizationEvidenceEvent, intersectWorlds_append,
      Rat.div_def, Rat.add_mul] using
      congrArg (fun q : Rat => q * (m.mu i w evidence)⁻¹) hNumAdd

/-- Package an admissible update of a strong model as a strong model without
adding any new probability axiom to the update interface. -/
def conditionalizeStrong
    {W Ag Atom : Type} [DecidableEq W]
    (m : StrongProbabilityModel W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m.toModel E) :
    StrongProbabilityModel W Ag Atom :=
  { toModel := conditionalize m.toModel E hAdm
    probability_integrity :=
      conditionalize_preserves_probabilityIntegrity
        m.toModel m.probability_integrity E hAdm }

/-- Recursive semantic classicality at every node relevant to the modal
recovery contract. At belief nodes it records the resulting classical value,
rather than naming threshold completeness as a separate certificate. -/
def ModalFormula.CompositionallyClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) : W → ModalFormula Atom Ag → Prop
  | w, ModalFormula.prop p => IsClassicalValue (m.val w p)
  | w, ModalFormula.not phi =>
      ModalFormula.CompositionallyClassicalAt m w phi
  | w, ModalFormula.and phi psi =>
      ModalFormula.CompositionallyClassicalAt m w phi ∧
      ModalFormula.CompositionallyClassicalAt m w psi
  | w, ModalFormula.bel i phi =>
      (∀ u, u ∈ m.R i w →
        ModalFormula.CompositionallyClassicalAt m u phi) ∧
      IsClassicalValue (evalModal m w (ModalFormula.bel i phi))
  | w, ModalFormula.know i phi =>
      ∀ u, u ∈ m.R i w →
        ModalFormula.CompositionallyClassicalAt m u phi
  | w, ModalFormula.poss i phi =>
      ∀ u, u ∈ m.R i w →
        ModalFormula.CompositionallyClassicalAt m u phi

/-- The recursive semantic predicate really guarantees a classical value at
its current node; this direction does not require probability integrity. -/
theorem evalModal_isClassical_of_compositionallyClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) :
    ∀ w,
      ModalFormula.CompositionallyClassicalAt m w phi →
      IsClassicalValue (evalModal m w phi) := by
  induction phi with
  | prop p =>
      intro w h
      exact h
  | not phi ih =>
      intro w h
      exact classicalValue_not _ (ih w h)
  | and phi psi ihPhi ihPsi =>
      intro w h
      exact classicalValue_and _ _ (ihPhi w h.1) (ihPsi w h.2)
  | bel i phi ih =>
      intro w h
      exact h.2
  | know i phi ih =>
      intro w h
      apply modalKnowledgeValue_classical_of_profile
        m i w (fun u => evalModal m u phi)
      intro u hu
      exact ih u (h u hu)
  | poss i phi ih =>
      intro w h
      apply modalRawPossibilityValue_classical_of_profile
        m i w (fun u => evalModal m u phi)
      intro u hu
      exact ih u (h u hu)

/-- Under finite probability integrity, the Gate-10 recovery certificate is
exactly recursive semantic classicality. The belief step is where
supermajority rules out the glut branch and completeness rules out the gap. -/
theorem compositionalRecoveryAt_iff_compositionallyClassicalAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : ModalFormula Atom Ag) :
    ∀ w,
      ModalFormula.CompositionalRecoveryAt m w phi ↔
        ModalFormula.CompositionallyClassicalAt m w phi := by
  induction phi with
  | prop p =>
      intro w
      rfl
  | not phi ih =>
      intro w
      exact ih w
  | and phi psi ihPhi ihPsi =>
      intro w
      constructor
      · intro h
        exact ⟨(ihPhi w).1 h.1, (ihPsi w).1 h.2⟩
      · intro h
        exact ⟨(ihPhi w).2 h.1, (ihPsi w).2 h.2⟩
  | bel i phi ih =>
      intro w
      constructor
      · intro h
        exact
          ⟨fun u hu => (ih u).1 (h.1 u hu),
            evalModal_isClassical_of_compositionalRecovery
              m hIntegrity (ModalFormula.bel i phi) w h⟩
      · intro h
        have hProfile :
            ∀ u, u ∈ m.R i w →
              IsClassicalValue (evalModal m u phi) := by
          intro u hu
          exact evalModal_isClassical_of_compositionallyClassicalAt
            m phi u (h.1 u hu)
        have hComplete :
            BeliefThresholdComplete m i w (fun u => evalModal m u phi) :=
          (probabilityIntegrity_classicalProfile_beliefClassical_iff_complete
            m hIntegrity i w (fun u => evalModal m u phi) hProfile).1 h.2
        exact ⟨fun u hu => (ih u).2 (h.1 u hu), hComplete⟩
  | know i phi ih =>
      intro w
      constructor <;> intro h u hu
      · exact (ih u).1 (h u hu)
      · exact (ih u).2 (h u hu)
  | poss i phi ih =>
      intro w
      constructor <;> intro h u hu
      · exact (ih u).1 (h u hu)
      · exact (ih u).2 (h u hu)

/-- Global recursive semantic classicality. Unlike mere top-level classicality,
this records the classical behavior of every reachable subformula node. -/
def ModalFormula.CompositionallyClassical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (phi : ModalFormula Atom Ag) : Prop :=
  ∀ w, ModalFormula.CompositionallyClassicalAt m w phi

/-- Global form of the certificate/semantic-classicality equivalence. -/
theorem compositionalRecovery_iff_compositionallyClassical
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecovery m phi ↔
      ModalFormula.CompositionallyClassical m phi := by
  constructor <;> intro h w
  · exact
      (compositionalRecoveryAt_iff_compositionallyClassicalAt
        m hIntegrity phi w).1 (h w)
  · exact
      (compositionalRecoveryAt_iff_compositionallyClassicalAt
        m hIntegrity phi w).2 (h w)

/-- Gate-13 exact posterior theorem. On an integrity-certified prior, the
existing admissible update remains integrity-certified. Hence, for a previously
recovered formula, absence of Gate-12 directed gaps is equivalent to recursive
semantic classicality throughout the posterior model. -/
theorem compositionalClassical_conditionalize_iff_noDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalFormula.CompositionalRecovery m phi) :
    ModalFormula.CompositionallyClassical (conditionalize m E hAdm) phi ↔
      ModalFormula.NoDirectionalGap m E hAdm phi := by
  have hUpdatedIntegrity :
      ModelProbabilityIntegrity (conditionalize m E hAdm) :=
    conditionalize_preserves_probabilityIntegrity m hIntegrity E hAdm
  rw [← compositionalRecovery_iff_compositionallyClassical
    (conditionalize m E hAdm) hUpdatedIntegrity phi]
  exact compositionalRecovery_conditionalize_iff_noDirectionalGap
    m hIntegrity E hAdm phi hBefore

/-- Observable corollary: no reachable directed gap pattern now suffices for
classical evaluation of the updated formula at every world. -/
theorem evalModal_conditionalize_isClassical_of_noDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi : ModalFormula Atom Ag)
    (hBefore : ModalFormula.CompositionalRecovery m phi)
    (hNoGap : ModalFormula.NoDirectionalGap m E hAdm phi) :
    ∀ w, IsClassicalValue (evalModal (conditionalize m E hAdm) w phi) := by
  have hCompositional :
      ModalFormula.CompositionallyClassical
        (conditionalize m E hAdm) phi :=
    (compositionalClassical_conditionalize_iff_noDirectionalGap
      m hIntegrity E hAdm phi hBefore).2 hNoGap
  intro w
  exact evalModal_isClassical_of_compositionallyClassicalAt
    (conditionalize m E hAdm) phi w (hCompositional w)

/-- Consequence-level payoff: the exact directional condition replaces the
stronger value-invariance/robustness premise previously used in Gate 11. -/
theorem modalST_iff_LP_after_conditionalize_of_noDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (phi psi : ModalFormula Atom Ag)
    (hBefore : ModalFormula.CompositionalRecovery m phi)
    (hNoGap : ModalFormula.NoDirectionalGap m E hAdm phi) :
    ModalST_SemanticEntailsIn (conditionalize m E hAdm) phi psi ↔
      ModalLP_SemanticEntailsIn (conditionalize m E hAdm) phi psi := by
  have hUpdatedIntegrity :=
    conditionalize_preserves_probabilityIntegrity m hIntegrity E hAdm
  have hUpdatedRecovery :=
    (compositionalRecovery_conditionalize_iff_noDirectionalGap
      m hIntegrity E hAdm phi hBefore).2 hNoGap
  exact modalST_iff_LP_of_compositionalRecovery
    (conditionalize m E hAdm) hUpdatedIntegrity phi psi hUpdatedRecovery

end PEL4
