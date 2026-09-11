import PEL4.EpistemicPathDependenceAsymptotic
import PEL4.ConditionalizationProbabilityIntegrity
import Init.Grind.Ring.Field

namespace PEL4

/-!
# Gate 30: Recovery confluence

Gate 29 proves that admissible evidence choice can make Recovery genuinely path
dependent.  Gate 30 asks for a positive boundary: when do two admissible update
orders necessarily agree?

For atomic evidence, the conditioning events are static because conditionalize
changes only `mu`.  Under finite probability integrity, conditioning first on
`p` and then on `q`, or first on `q` and then on `p`, yields the same probability
on every well-formed local event.  Because every event actually inspected by the
modal evaluator is a duplicate-free subset of an accessibility range, this is
enough for complete modal observational equivalence and hence Recovery
confluence.

The distinction between full `Model` equality and modal observational equality
is deliberate. `FiniteSet` is currently represented by `List`, and the integrity
contract constrains duplicate-free event presentations. Arbitrary duplicate
lists are not semantically observable by the modal language and need not receive
identical raw `mu` values.
-/

/-- Set-like commutativity of list-filter intersection. -/
theorem intersectWorlds_comm_extensional
    {W : Type} [DecidableEq W]
    (A B : FiniteSet W) :
    FiniteEventExtEq (intersectWorlds A B) (intersectWorlds B A) := by
  intro x
  simp [intersectWorlds, and_comm]

/-- The order of two successive right-hand intersections is extensionally
irrelevant. -/
theorem intersectWorlds_right_swap_extensional
    {W : Type} [DecidableEq W]
    (S A B : FiniteSet W) :
    FiniteEventExtEq
      (intersectWorlds (intersectWorlds S A) B)
      (intersectWorlds (intersectWorlds S B) A) := by
  intro x
  simp [intersectWorlds, and_assoc, and_left_comm, and_comm]

/-- Quotient cancellation used by two-step conditioning. -/
theorem rat_div_div_same_den_cancel
    (a b d : Rat) (hb : b ≠ 0) :
    (a / b) / (d / b) = a / d := by
  rw [Field.div_div_right]
  rw [Rat.div_mul_cancel hb]

/-- Once atomic evidence is known admissible, its raw conditionalized measure
is the ordinary quotient by its positive event mass. -/
theorem conditionalize_mu_prop_eq_div
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (i : Ag) (w : W) (S : FiniteSet W) :
    conditionalize_mu m i w (Formula.prop p) S =
      m.mu i w
          (intersectWorlds S
            (filterWorlds (m.R i w)
              (fun u => (eval m u (Formula.prop p)).pos))) /
        m.mu i w
          (filterWorlds (m.R i w)
            (fun u => (eval m u (Formula.prop p)).pos)) := by
  have hDenNe :
      m.mu i w
        (filterWorlds (m.R i w)
          (fun u => (eval m u (Formula.prop p)).pos)) ≠ 0 := by
    simpa [conditionalizationEvidenceMass] using hAdm.positive_mass i w
  simp only [conditionalize_mu, beq_iff_eq]
  rw [if_neg hDenNe]

/-- Two admissible atomic conditioning orders agree on every well-formed local
event of an integrity-certified prior. -/
theorem conditionalize_two_atoms_measure_eq_on_event
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
    (i : Ag) (w : W) (S : FiniteSet W)
    (hSNodup : S.Nodup)
    (hSSub : FiniteEventSubset S (m.R i w)) :
    (conditionalize
        (conditionalize m (Formula.prop p) hP)
        (Formula.prop q) hQAfterP).mu i w S =
      (conditionalize
        (conditionalize m (Formula.prop q) hQ)
        (Formula.prop p) hPAfterQ).mu i w S := by
  let P := filterWorlds (m.R i w)
    (fun u => (eval m u (Formula.prop p)).pos)
  let Q := filterWorlds (m.R i w)
    (fun u => (eval m u (Formula.prop q)).pos)
  have hPNe : m.mu i w P ≠ 0 := by
    simpa [P, conditionalizationEvidenceMass] using hP.positive_mass i w
  have hQNe : m.mu i w Q ≠ 0 := by
    simpa [Q, conditionalizationEvidenceMass] using hQ.positive_mass i w
  have hQAfterPNe :
      (conditionalize m (Formula.prop p) hP).mu i w Q ≠ 0 := by
    simpa [Q, conditionalizationEvidenceMass] using hQAfterP.positive_mass i w
  have hPAfterQNe :
      (conditionalize m (Formula.prop q) hQ).mu i w P ≠ 0 := by
    simpa [P, conditionalizationEvidenceMass] using hPAfterQ.positive_mass i w

  have hSupportNodup : (m.R i w).Nodup :=
    (hIntegrity i w).support_nodup
  have hPNodup : P.Nodup := by
    simpa [P] using filterWorlds_nodup (m.R i w)
      (fun u => (eval m u (Formula.prop p)).pos) hSupportNodup
  have hQNodup : Q.Nodup := by
    simpa [Q] using filterWorlds_nodup (m.R i w)
      (fun u => (eval m u (Formula.prop q)).pos) hSupportNodup
  have hPSub : FiniteEventSubset P (m.R i w) := by
    intro x hx
    exact (List.mem_filter.mp hx).1
  have hQSub : FiniteEventSubset Q (m.R i w) := by
    intro x hx
    exact (List.mem_filter.mp hx).1

  have hNumEq :
      m.mu i w (intersectWorlds (intersectWorlds S Q) P) =
        m.mu i w (intersectWorlds (intersectWorlds S P) Q) := by
    apply (hIntegrity i w).extensional
    · exact intersectWorlds_nodup (intersectWorlds S Q) P
        (intersectWorlds_nodup S Q hSNodup)
    · exact intersectWorlds_nodup (intersectWorlds S P) Q
        (intersectWorlds_nodup S P hSNodup)
    · intro x hx
      exact hSSub x
        (intersectWorlds_subset_left S Q x
          (intersectWorlds_subset_left (intersectWorlds S Q) P x hx))
    · intro x hx
      exact hSSub x
        (intersectWorlds_subset_left S P x
          (intersectWorlds_subset_left (intersectWorlds S P) Q x hx))
    · exact intersectWorlds_right_swap_extensional S Q P

  have hDenEq :
      m.mu i w (intersectWorlds Q P) =
        m.mu i w (intersectWorlds P Q) := by
    apply (hIntegrity i w).extensional
    · exact intersectWorlds_nodup Q P hQNodup
    · exact intersectWorlds_nodup P Q hPNodup
    · intro x hx
      exact hQSub x (intersectWorlds_subset_left Q P x hx)
    · intro x hx
      exact hPSub x (intersectWorlds_subset_left P Q x hx)
    · exact intersectWorlds_comm_extensional Q P

  change
    conditionalize_mu (conditionalize m (Formula.prop p) hP)
        i w (Formula.prop q) S =
      conditionalize_mu (conditionalize m (Formula.prop q) hQ)
        i w (Formula.prop p) S
  simp only [conditionalize_mu, beq_iff_eq]
  change
    (if (conditionalize m (Formula.prop p) hP).mu i w Q = 0 then 0
      else
        (conditionalize m (Formula.prop p) hP).mu i w
            (intersectWorlds S Q) /
          (conditionalize m (Formula.prop p) hP).mu i w Q) =
    (if (conditionalize m (Formula.prop q) hQ).mu i w P = 0 then 0
      else
        (conditionalize m (Formula.prop q) hQ).mu i w
            (intersectWorlds S P) /
          (conditionalize m (Formula.prop q) hQ).mu i w P)
  rw [if_neg hQAfterPNe, if_neg hPAfterQNe]
  change
    (conditionalize_mu m i w (Formula.prop p) (intersectWorlds S Q)) /
        (conditionalize_mu m i w (Formula.prop p) Q) =
      (conditionalize_mu m i w (Formula.prop q) (intersectWorlds S P)) /
        (conditionalize_mu m i w (Formula.prop q) P)
  rw [conditionalize_mu_prop_eq_div m p hP i w (intersectWorlds S Q)]
  rw [conditionalize_mu_prop_eq_div m p hP i w Q]
  rw [conditionalize_mu_prop_eq_div m q hQ i w (intersectWorlds S P)]
  rw [conditionalize_mu_prop_eq_div m q hQ i w P]
  change
    (m.mu i w (intersectWorlds (intersectWorlds S Q) P) / m.mu i w P) /
        (m.mu i w (intersectWorlds Q P) / m.mu i w P) =
      (m.mu i w (intersectWorlds (intersectWorlds S P) Q) / m.mu i w Q) /
        (m.mu i w (intersectWorlds P Q) / m.mu i w Q)
  rw [rat_div_div_same_den_cancel _ _ _ hPNe]
  rw [rat_div_div_same_den_cancel _ _ _ hQNe]
  rw [hNumEq, hDenEq]

/-- Models can be modally indistinguishable even when their raw list-indexed
measure functions are not propositionally equal on malformed duplicate lists. -/
structure ModalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom) : Prop where
  worlds_eq : n.worlds = m.worlds
  accessibility_eq : n.R = m.R
  valuation_eq : n.val = m.val
  threshold_eq : n.c = m.c
  measure_eq_on_event :
    ∀ (i : Ag) (w : W) (S : FiniteSet W),
      S.Nodup →
      FiniteEventSubset S (m.R i w) →
      n.mu i w S = m.mu i w S

/-- Belief is invariant under modal observational equivalence. -/
theorem belief_eq_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (vM vN : W → FDEValue)
    (hV : vN = vM) :
    belief n i w vN = belief m i w vM := by
  have hR : n.R i w = m.R i w := by
    exact congrFun (congrFun hEq.accessibility_eq i) w
  have hC : n.c i = m.c i := by
    exact congrFun hEq.threshold_eq i
  let P := filterWorlds (m.R i w) (fun u => (vM u).pos)
  let N := filterWorlds (m.R i w) (fun u => (vM u).neg)
  have hSupportNodup := (hIntegrity i w).support_nodup
  have hPNodup : P.Nodup := by
    simpa [P] using filterWorlds_nodup (m.R i w)
      (fun u => (vM u).pos) hSupportNodup
  have hNNodup : N.Nodup := by
    simpa [N] using filterWorlds_nodup (m.R i w)
      (fun u => (vM u).neg) hSupportNodup
  have hPSub : FiniteEventSubset P (m.R i w) := by
    intro x hx
    exact (List.mem_filter.mp hx).1
  have hNSub : FiniteEventSubset N (m.R i w) := by
    intro x hx
    exact (List.mem_filter.mp hx).1
  have hPMass := hEq.measure_eq_on_event i w P hPNodup hPSub
  have hNMass := hEq.measure_eq_on_event i w N hNNodup hNSub
  unfold belief
  rw [hR, hV, hC]
  change
    { pos := n.mu i w P ≥ m.c i, neg := n.mu i w N ≥ m.c i } =
      { pos := m.mu i w P ≥ m.c i, neg := m.mu i w N ≥ m.c i }
  rw [hPMass, hNMass]

/-- Every modal formula has the same complete FDE value in observationally
equivalent models. -/
theorem evalModal_eq_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrity : ModelProbabilityIntegrity m) :
    ∀ (phi : ModalFormula Atom Ag) (w : W),
      evalModal n w phi = evalModal m w phi := by
  intro phi
  induction phi with
  | prop p =>
      intro w
      change n.val w p = m.val w p
      exact congrFun (congrFun hEq.valuation_eq w) p
  | not phi ih =>
      intro w
      change FDEValue.not (evalModal n w phi) =
        FDEValue.not (evalModal m w phi)
      rw [ih w]
  | and phi psi ihPhi ihPsi =>
      intro w
      change FDEValue.and (evalModal n w phi) (evalModal n w psi) =
        FDEValue.and (evalModal m w phi) (evalModal m w psi)
      rw [ihPhi w, ihPsi w]
  | bel i phi ih =>
      intro w
      apply belief_eq_of_modalObservationEquivalent
        hEq hIntegrity i w
        (fun u => evalModal m u phi)
        (fun u => evalModal n u phi)
      funext u
      exact ih u
  | know i phi ih =>
      intro w
      apply modalKnowledgeValue_congr
        m n i w
        (fun u => evalModal m u phi)
        (fun u => evalModal n u phi)
      · exact congrFun (congrFun hEq.accessibility_eq i) w
      · funext u
        exact ih u
  | poss i phi ih =>
      intro w
      apply modalRawPossibilityValue_congr
        m n i w
        (fun u => evalModal m u phi)
        (fun u => evalModal n u phi)
      · exact congrFun (congrFun hEq.accessibility_eq i) w
      · funext u
        exact ih u

/-- Threshold completeness is modally observable and therefore invariant under
observational equivalence. -/
theorem beliefThresholdComplete_iff_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrity : ModelProbabilityIntegrity m)
    (i : Ag) (w : W)
    (vM vN : W → FDEValue)
    (hV : vN = vM) :
    BeliefThresholdComplete n i w vN ↔
      BeliefThresholdComplete m i w vM := by
  have hBel := belief_eq_of_modalObservationEquivalent
    hEq hIntegrity i w vM vN hV
  have hPos :
      beliefPositiveThresholdBit n i w vN =
        beliefPositiveThresholdBit m i w vM := by
    have := congrArg FDEValue.pos hBel
    simpa [belief_eq_thresholdBits] using this
  have hNeg :
      beliefNegativeThresholdBit n i w vN =
        beliefNegativeThresholdBit m i w vM := by
    have := congrArg FDEValue.neg hBel
    simpa [belief_eq_thresholdBits] using this
  unfold BeliefThresholdComplete
  rw [hPos, hNeg]

/-- The recursive Recovery contract itself is invariant under modal
observational equivalence. -/
theorem compositionalRecoveryAt_iff_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrity : ModelProbabilityIntegrity m) :
    ∀ (phi : ModalFormula Atom Ag) (w : W),
      ModalFormula.CompositionalRecoveryAt n w phi ↔
        ModalFormula.CompositionalRecoveryAt m w phi := by
  intro phi
  induction phi with
  | prop p =>
      intro w
      change IsClassicalValue (n.val w p) ↔ IsClassicalValue (m.val w p)
      rw [congrFun (congrFun hEq.valuation_eq w) p]
  | not phi ih =>
      intro w
      exact ih w
  | and phi psi ihPhi ihPsi =>
      intro w
      exact and_congr (ihPhi w) (ihPsi w)
  | bel i phi ih =>
      intro w
      have hR : n.R i w = m.R i w :=
        congrFun (congrFun hEq.accessibility_eq i) w
      have hValues :
          (fun u => evalModal n u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact evalModal_eq_of_modalObservationEquivalent hEq hIntegrity phi u
      constructor
      · intro h
        constructor
        · intro u hu
          apply (ih u).1
          apply h.1 u
          rwa [hR]
        · exact
            (beliefThresholdComplete_iff_of_modalObservationEquivalent
              hEq hIntegrity i w
              (fun u => evalModal m u phi)
              (fun u => evalModal n u phi) hValues).1 h.2
      · intro h
        constructor
        · intro u hu
          apply (ih u).2
          apply h.1 u
          rwa [← hR]
        · exact
            (beliefThresholdComplete_iff_of_modalObservationEquivalent
              hEq hIntegrity i w
              (fun u => evalModal m u phi)
              (fun u => evalModal n u phi) hValues).2 h.2
  | know i phi ih =>
      intro w
      have hR : n.R i w = m.R i w :=
        congrFun (congrFun hEq.accessibility_eq i) w
      constructor
      · intro h u hu
        apply (ih u).1
        apply h u
        rwa [hR]
      · intro h u hu
        apply (ih u).2
        apply h u
        rwa [← hR]
  | poss i phi ih =>
      intro w
      have hR : n.R i w = m.R i w :=
        congrFun (congrFun hEq.accessibility_eq i) w
      constructor
      · intro h u hu
        apply (ih u).1
        apply h u
        rwa [hR]
      · intro h u hu
        apply (ih u).2
        apply h u
        rwa [← hR]

/-- Global Recovery has the same truth value in observationally equivalent
models. -/
theorem compositionalRecovery_iff_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrity : ModelProbabilityIntegrity m)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecovery n phi ↔
      ModalFormula.CompositionalRecovery m phi := by
  constructor
  · intro h w
    exact
      (compositionalRecoveryAt_iff_of_modalObservationEquivalent
        hEq hIntegrity phi w).1 (h w)
  · intro h w
    exact
      (compositionalRecoveryAt_iff_of_modalObservationEquivalent
        hEq hIntegrity phi w).2 (h w)

/-- Main concrete confluence certificate: the two atomic update orders are
modally observationally equivalent. -/
theorem conditionalize_two_atoms_observationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (p q : Atom)
    (hP : ConditionalizationAdmissible m (Formula.prop p))
    (hQ : ConditionalizationAdmissible m (Formula.prop q))
    (hQAfterP : ConditionalizationAdmissible
      (conditionalize m (Formula.prop p) hP) (Formula.prop q))
    (hPAfterQ : ConditionalizationAdmissible
      (conditionalize m (Formula.prop q) hQ) (Formula.prop p)) :
    ModalObservationEquivalent
      (conditionalize
        (conditionalize m (Formula.prop p) hP)
        (Formula.prop q) hQAfterP)
      (conditionalize
        (conditionalize m (Formula.prop q) hQ)
        (Formula.prop p) hPAfterQ) := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i w S hSNodup hSSub
    symm
    exact conditionalize_two_atoms_measure_eq_on_event
      m hIntegrity p q hP hQ hQAfterP hPAfterQ i w S hSNodup hSSub

/-- Gate-30 recovery confluence theorem: whenever both atomic update orders are
admissible, they agree on the Recovery status of every modal formula. -/
theorem conditionalize_two_atoms_recovery_confluent
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
  let mPQ := conditionalize
    (conditionalize m (Formula.prop p) hP)
    (Formula.prop q) hQAfterP
  let mQP := conditionalize
    (conditionalize m (Formula.prop q) hQ)
    (Formula.prop p) hPAfterQ
  have hIntP := conditionalize_preserves_probabilityIntegrity
    m hIntegrity (Formula.prop p) hP
  have hIntPQ := conditionalize_preserves_probabilityIntegrity
    (conditionalize m (Formula.prop p) hP) hIntP
    (Formula.prop q) hQAfterP
  have hObs : ModalObservationEquivalent mPQ mQP := by
    simpa [mPQ, mQP] using
      conditionalize_two_atoms_observationEquivalent
        m hIntegrity p q hP hQ hQAfterP hPAfterQ
  exact
    (compositionalRecovery_iff_of_modalObservationEquivalent
      hObs hIntPQ phi).symm

end PEL4
