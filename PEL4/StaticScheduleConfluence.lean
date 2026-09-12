import PEL4.SemanticFeedbackBoundary
import PEL4.RecoveryConfluence

namespace PEL4

/-!
# Gate 38: static schedule confluence

Gate 30 established confluence for two atomic conditioning events. Gate 36 then
identified a larger static fragment: every belief-free evidence formula keeps
exactly the same positive extension under probability-only conditionalization.

Gate 38 combines these results. The first layer proves that any two belief-free
evidence formulas commute up to complete modal observational equivalence,
provided both sequential orders are admissible and the prior satisfies finite
probability integrity.

This pairwise theorem is the local swap generator needed for finite schedule
normalization. The finite-permutation closure is developed after this generator
is verified.
-/

/-- Generic quotient form of conditionalization once admissibility supplies a
nonzero evidence denominator. -/
theorem conditionalize_mu_eq_div
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (S : FiniteSet W) :
    conditionalize_mu m i w E S =
      m.mu i w
          (intersectWorlds S (conditionalizationEvidenceEvent m i w E)) /
        m.mu i w (conditionalizationEvidenceEvent m i w E) := by
  have hDenNe :
      m.mu i w
        (filterWorlds (m.R i w) (fun u => (eval m u E).pos)) ≠ 0 := by
    simpa [conditionalizationEvidenceMass] using hAdm.positive_mass i w
  simp only [conditionalize_mu, beq_iff_eq]
  rw [if_neg hDenNe]
  rfl

/-- Two belief-free evidence formulas, processed in either admissible order,
agree on every well-formed local event. -/
theorem conditionalize_two_beliefFree_measure_eq_on_event
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hPFree : P.BeliefFree)
    (hQFree : Q.BeliefFree)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P)
    (i : Ag) (w : W) (S : FiniteSet W)
    (hSNodup : S.Nodup)
    (hSSub : FiniteEventSubset S (m.R i w)) :
    (conditionalize (conditionalize m P hP) Q hQAfterP).mu i w S =
      (conditionalize (conditionalize m Q hQ) P hPAfterQ).mu i w S := by
  let PE := conditionalizationEvidenceEvent m i w P
  let QE := conditionalizationEvidenceEvent m i w Q

  have hPStable :=
    beliefFree_evidenceExtensionStableUnder m Q P hQ hPFree
  have hQStable :=
    beliefFree_evidenceExtensionStableUnder m P Q hP hQFree

  have hPNe : m.mu i w PE ≠ 0 := by
    simpa [PE, conditionalizationEvidenceMass, conditionalizationEvidenceEvent]
      using hP.positive_mass i w
  have hQNe : m.mu i w QE ≠ 0 := by
    simpa [QE, conditionalizationEvidenceMass, conditionalizationEvidenceEvent]
      using hQ.positive_mass i w

  have hQAfterPNe : (conditionalize m P hP).mu i w QE ≠ 0 := by
    have hRaw := hQAfterP.positive_mass i w
    change
      (conditionalize m P hP).mu i w
        (conditionalizationEvidenceEvent (conditionalize m P hP) i w Q) ≠ 0 at hRaw
    rw [hQStable i w] at hRaw
    simpa [QE] using hRaw

  have hPAfterQNe : (conditionalize m Q hQ).mu i w PE ≠ 0 := by
    have hRaw := hPAfterQ.positive_mass i w
    change
      (conditionalize m Q hQ).mu i w
        (conditionalizationEvidenceEvent (conditionalize m Q hQ) i w P) ≠ 0 at hRaw
    rw [hPStable i w] at hRaw
    simpa [PE] using hRaw

  have hPENodup : PE.Nodup := by
    simpa [PE] using conditionalizationEvidenceEvent_nodup m hIntegrity i w P
  have hQENodup : QE.Nodup := by
    simpa [QE] using conditionalizationEvidenceEvent_nodup m hIntegrity i w Q
  have hPESub : FiniteEventSubset PE (m.R i w) := by
    simpa [PE] using conditionalizationEvidenceEvent_subset m i w P
  have hQESub : FiniteEventSubset QE (m.R i w) := by
    simpa [QE] using conditionalizationEvidenceEvent_subset m i w Q

  have hNumEq :
      m.mu i w (intersectWorlds (intersectWorlds S QE) PE) =
        m.mu i w (intersectWorlds (intersectWorlds S PE) QE) := by
    apply (hIntegrity i w).extensional
    · exact intersectWorlds_nodup (intersectWorlds S QE) PE
        (intersectWorlds_nodup S QE hSNodup)
    · exact intersectWorlds_nodup (intersectWorlds S PE) QE
        (intersectWorlds_nodup S PE hSNodup)
    · intro x hx
      exact hSSub x
        (intersectWorlds_subset_left S QE x
          (intersectWorlds_subset_left (intersectWorlds S QE) PE x hx))
    · intro x hx
      exact hSSub x
        (intersectWorlds_subset_left S PE x
          (intersectWorlds_subset_left (intersectWorlds S PE) QE x hx))
    · exact intersectWorlds_right_swap_extensional S QE PE

  have hDenEq :
      m.mu i w (intersectWorlds QE PE) =
        m.mu i w (intersectWorlds PE QE) := by
    apply (hIntegrity i w).extensional
    · exact intersectWorlds_nodup QE PE hQENodup
    · exact intersectWorlds_nodup PE QE hPENodup
    · intro x hx
      exact hQESub x (intersectWorlds_subset_left QE PE x hx)
    · intro x hx
      exact hPESub x (intersectWorlds_subset_left PE QE x hx)
    · exact intersectWorlds_comm_extensional QE PE

  change
    conditionalize_mu (conditionalize m P hP) i w Q S =
      conditionalize_mu (conditionalize m Q hQ) i w P S

  rw [conditionalize_mu_eq_div (conditionalize m P hP) Q hQAfterP i w S]
  rw [conditionalize_mu_eq_div (conditionalize m Q hQ) P hPAfterQ i w S]
  rw [hQStable i w, hPStable i w]
  change
    (conditionalize_mu m i w P (intersectWorlds S QE)) /
        (conditionalize_mu m i w P QE) =
      (conditionalize_mu m i w Q (intersectWorlds S PE)) /
        (conditionalize_mu m i w Q PE)

  rw [conditionalize_mu_eq_div m P hP i w (intersectWorlds S QE)]
  rw [conditionalize_mu_eq_div m P hP i w QE]
  rw [conditionalize_mu_eq_div m Q hQ i w (intersectWorlds S PE)]
  rw [conditionalize_mu_eq_div m Q hQ i w PE]
  change
    (m.mu i w (intersectWorlds (intersectWorlds S QE) PE) / m.mu i w PE) /
        (m.mu i w (intersectWorlds QE PE) / m.mu i w PE) =
      (m.mu i w (intersectWorlds (intersectWorlds S PE) QE) / m.mu i w QE) /
        (m.mu i w (intersectWorlds PE QE) / m.mu i w QE)
  rw [rat_div_div_same_den_cancel _ _ _ hPNe]
  rw [rat_div_div_same_den_cancel _ _ _ hQNe]
  rw [hNumEq, hDenEq]

/-- Pairwise Gate-38 confluence certificate for arbitrary belief-free evidence. -/
theorem conditionalize_two_beliefFree_observationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hPFree : P.BeliefFree)
    (hQFree : Q.BeliefFree)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P) :
    ModalObservationEquivalent
      (conditionalize (conditionalize m P hP) Q hQAfterP)
      (conditionalize (conditionalize m Q hQ) P hPAfterQ) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i w S hSNodup hSSub
    symm
    exact conditionalize_two_beliefFree_measure_eq_on_event
      m hIntegrity P Q hPFree hQFree hP hQ hQAfterP hPAfterQ
      i w S hSNodup hSSub

/-- Any two belief-free evidence formulas agree on the Recovery status of every
modal target after reversing their admissible processing order. -/
theorem conditionalize_two_beliefFree_recovery_confluent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hPFree : P.BeliefFree)
    (hQFree : Q.BeliefFree)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecovery
      (conditionalize (conditionalize m P hP) Q hQAfterP) phi ↔
    ModalFormula.CompositionalRecovery
      (conditionalize (conditionalize m Q hQ) P hPAfterQ) phi := by
  let mPQ := conditionalize (conditionalize m P hP) Q hQAfterP
  let mQP := conditionalize (conditionalize m Q hQ) P hPAfterQ
  have hIntP := conditionalize_preserves_probabilityIntegrity m hIntegrity P hP
  have hIntPQ := conditionalize_preserves_probabilityIntegrity
    (conditionalize m P hP) hIntP Q hQAfterP
  have hObs : ModalObservationEquivalent mPQ mQP := by
    simpa [mPQ, mQP] using
      conditionalize_two_beliefFree_observationEquivalent
        m hIntegrity P Q hPFree hQFree hP hQ hQAfterP hPAfterQ
  exact
    (compositionalRecovery_iff_of_modalObservationEquivalent
      hObs hIntPQ phi).symm

/-- Gate 30 is recovered as the atomic special case of the larger belief-free
static fragment. -/
theorem gate38_atomic_confluence_as_special_case
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (p q : Atom)
    (hP : ConditionalizationAdmissible m (Formula.prop p))
    (hQ : ConditionalizationAdmissible m (Formula.prop q))
    (hQAfterP : ConditionalizationAdmissible
      (conditionalize m (Formula.prop p) hP) (Formula.prop q))
    (hPAfterQ : ConditionalizationAdmissible
      (conditionalize m (Formula.prop q) hQ) (Formula.prop p))
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecovery
      (conditionalize
        (conditionalize m (Formula.prop p) hP)
        (Formula.prop q) hQAfterP) phi ↔
    ModalFormula.CompositionalRecovery
      (conditionalize
        (conditionalize m (Formula.prop q) hQ)
        (Formula.prop p) hPAfterQ) phi := by
  exact conditionalize_two_beliefFree_recovery_confluent
    m hIntegrity (Formula.prop p) (Formula.prop q)
    (by trivial) (by trivial) hP hQ hQAfterP hPAfterQ phi

end PEL4
