import PEL4.StaticScheduleConfluence
import PEL4.EpistemicStateSufficiency

namespace PEL4

/-!
# Gate 40: strong hysteresis boundary

Gate 36 gave a syntactic sufficient condition for static evidence: belief-free
formulas keep their positive extension under Conditionalization. Gate 38 used
that fact to prove confluence. Gate 40 removes the syntax restriction and states
the semantic boundary directly.

Two arbitrary evidence formulas may contain belief operators. If, nevertheless,
each formula keeps the same positive extension after the other update, then the
two update orders are modally observationally equivalent and cannot disagree on
Recovery. Hence Recovery hysteresis requires semantic extension feedback in at
least one direction.
-/

/-- Generic two-update measure confluence under explicit mutual extension
stability. No belief-free assumption is used. -/
theorem conditionalize_two_extensionStable_measure_eq_on_event
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P)
    (hPStableAfterQ : EvidenceExtensionStableUnder m Q P hQ)
    (hQStableAfterP : EvidenceExtensionStableUnder m P Q hP)
    (i : Ag) (w : W) (S : FiniteSet W)
    (hSNodup : S.Nodup)
    (hSSub : FiniteEventSubset S (m.R i w)) :
    (conditionalize (conditionalize m P hP) Q hQAfterP).mu i w S =
      (conditionalize (conditionalize m Q hQ) P hPAfterQ).mu i w S := by
  let PE := conditionalizationEvidenceEvent m i w P
  let QE := conditionalizationEvidenceEvent m i w Q

  have hPNe : m.mu i w PE ≠ 0 := by
    simpa [PE, conditionalizationEvidenceMass, conditionalizationEvidenceEvent]
      using hP.positive_mass i w
  have hQNe : m.mu i w QE ≠ 0 := by
    simpa [QE, conditionalizationEvidenceMass, conditionalizationEvidenceEvent]
      using hQ.positive_mass i w

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
  rw [hQStableAfterP i w, hPStableAfterQ i w]
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

/-- Explicit mutual extension stability is sufficient for complete modal
observational confluence of two arbitrary evidence formulas. -/
theorem conditionalize_two_extensionStable_observationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P)
    (hPStableAfterQ : EvidenceExtensionStableUnder m Q P hQ)
    (hQStableAfterP : EvidenceExtensionStableUnder m P Q hP) :
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
    exact conditionalize_two_extensionStable_measure_eq_on_event
      m hIntegrity P Q hP hQ hQAfterP hPAfterQ
      hPStableAfterQ hQStableAfterP i w S hSNodup hSSub

/-- Strong no-hysteresis theorem: arbitrary evidence formulas cannot differ in
Recovery by order if their extensional content is mutually update-stable. -/
theorem conditionalize_two_extensionStable_recovery_confluent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P)
    (hPStableAfterQ : EvidenceExtensionStableUnder m Q P hQ)
    (hQStableAfterP : EvidenceExtensionStableUnder m P Q hP)
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
      conditionalize_two_extensionStable_observationEquivalent
        m hIntegrity P Q hP hQ hQAfterP hPAfterQ
        hPStableAfterQ hQStableAfterP
  exact
    (compositionalRecovery_iff_of_modalObservationEquivalent
      hObs hIntPQ phi).symm

/-- Therefore any concrete Recovery hysteresis witness must violate mutual
extension stability in at least one direction. This is the semantic necessity
statement missing from the earlier syntactic boundary. -/
theorem recovery_hysteresis_implies_extension_feedback
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (hP : ConditionalizationAdmissible m P)
    (hQ : ConditionalizationAdmissible m Q)
    (hQAfterP : ConditionalizationAdmissible (conditionalize m P hP) Q)
    (hPAfterQ : ConditionalizationAdmissible (conditionalize m Q hQ) P)
    (phi : ModalFormula Atom Ag)
    (hHysteresis :
      (ModalFormula.CompositionalRecovery
          (conditionalize (conditionalize m P hP) Q hQAfterP) phi ∧
        ¬ ModalFormula.CompositionalRecovery
          (conditionalize (conditionalize m Q hQ) P hPAfterQ) phi) ∨
      (ModalFormula.CompositionalRecovery
          (conditionalize (conditionalize m Q hQ) P hPAfterQ) phi ∧
        ¬ ModalFormula.CompositionalRecovery
          (conditionalize (conditionalize m P hP) Q hQAfterP) phi)) :
    ¬ (EvidenceExtensionStableUnder m Q P hQ ∧
       EvidenceExtensionStableUnder m P Q hP) := by
  intro hStable
  have hConfluent := conditionalize_two_extensionStable_recovery_confluent
    m hIntegrity P Q hP hQ hQAfterP hPAfterQ hStable.1 hStable.2 phi
  rcases hHysteresis with hPQ | hQP
  · exact hPQ.2 (hConfluent.mp hPQ.1)
  · exact hQP.2 (hConfluent.mpr hQP.1)

/-- Gate 33 realizes the required semantic feedback explicitly: `B p` is not
extension-stable under the preceding atomic update `e`. -/
theorem gate40_gate33_violates_mutual_extension_stability :
    ¬ (EvidenceExtensionStableUnder
          DynamicInstabilityModel dynamicInstabilityEvidence
          gate33BelPEvidence dynamic_instability_evidence_admissible ∧
       EvidenceExtensionStableUnder
          DynamicInstabilityModel gate33BelPEvidence
          dynamicInstabilityEvidence gate33_belP_initial_admissible) := by
  intro hStable
  exact (evidenceExtensionStable_not_sensitive
    DynamicInstabilityModel dynamicInstabilityEvidence gate33BelPEvidence
    dynamic_instability_evidence_admissible hStable.1)
    gate36_gate33_belP_extension_sensitive

/-!
## Gate-40 conclusion

The boundary is now semantic rather than merely syntactic:

```text
mutually fixed evidence extensions
  => Bayes order confluence up to all modal observations
  => identical Recovery status.

Recovery hysteresis
  => at least one evidence extension is changed by the other update.
```

Belief operators are therefore not themselves the essence of hysteresis. Their
role in Gate 33 is that they make semantic extension feedback possible. A
belief-containing formula that happens to remain extension-stable still lies on
the confluent side of the boundary.
-/

end PEL4
