import PEL4.StaticScheduleConfluence

namespace PEL4

/-!
# Gate 38, finite layer: suffix stability and adjacent schedule swaps

The pairwise Gate-38 theorem supplies a local swap. This file proves that modal
observational equivalence survives any common belief-free suffix. Consequently
a pair of adjacent belief-free updates can be swapped inside an otherwise
identical admissible finite schedule without changing the final modal
observations or Recovery status.
-/

/-- Belief-free evidence evaluation is determined by valuation alone, so it is
invariant across modally observationally equivalent models. -/
theorem eval_beliefFree_eq_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n) :
    ∀ (phi : Formula Atom Ag), phi.BeliefFree → ∀ w,
      eval n w phi = eval m w phi := by
  intro phi hFree
  induction phi with
  | prop p =>
      intro w
      change n.val w p = m.val w p
      exact congrFun (congrFun hEq.valuation_eq w) p
  | not phi ih =>
      intro w
      simp only [Formula.BeliefFree] at hFree
      change FDEValue.not (eval n w phi) = FDEValue.not (eval m w phi)
      rw [ih hFree w]
  | and phi psi ihPhi ihPsi =>
      intro w
      simp only [Formula.BeliefFree] at hFree
      change FDEValue.and (eval n w phi) (eval n w psi) =
        FDEValue.and (eval m w phi) (eval m w psi)
      rw [ihPhi hFree.1 w, ihPsi hFree.2 w]
  | bel i phi ih =>
      simp only [Formula.BeliefFree] at hFree

/-- The positive extension of belief-free evidence agrees across observationally
equivalent models. -/
theorem beliefFree_evidenceEvent_eq_of_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (E : Formula Atom Ag) (hFree : E.BeliefFree)
    (i : Ag) (w : W) :
    conditionalizationEvidenceEvent n i w E =
      conditionalizationEvidenceEvent m i w E := by
  unfold conditionalizationEvidenceEvent
  have hR : n.R i w = m.R i w :=
    congrFun (congrFun hEq.accessibility_eq i) w
  have hPred :
      (fun u => (eval n u E).pos) = (fun u => (eval m u E).pos) := by
    funext u
    rw [eval_beliefFree_eq_of_modalObservationEquivalent hEq E hFree u]
  rw [hR, hPred]

/-- A common belief-free update preserves modal observational equivalence. -/
theorem conditionalize_beliefFree_preserves_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n : Model W Ag Atom}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrityM : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag) (hFree : E.BeliefFree)
    (hM : ConditionalizationAdmissible m E)
    (hN : ConditionalizationAdmissible n E) :
    ModalObservationEquivalent
      (conditionalize m E hM) (conditionalize n E hN) := by
  constructor
  · simpa [conditionalize] using hEq.worlds_eq
  · simpa [conditionalize] using hEq.accessibility_eq
  · simpa [conditionalize] using hEq.valuation_eq
  · simpa [conditionalize] using hEq.threshold_eq
  · intro i w S hSNodup hSSub
    have hEvent :=
      beliefFree_evidenceEvent_eq_of_modalObservationEquivalent hEq E hFree i w
    let eventM := conditionalizationEvidenceEvent m i w E
    have hEventNodup : eventM.Nodup := by
      simpa [eventM] using
        conditionalizationEvidenceEvent_nodup m hIntegrityM i w E
    have hEventSub : FiniteEventSubset eventM (m.R i w) := by
      simpa [eventM] using conditionalizationEvidenceEvent_subset m i w E
    have hNumNodup : (intersectWorlds S eventM).Nodup :=
      intersectWorlds_nodup S eventM hSNodup
    have hNumSub : FiniteEventSubset (intersectWorlds S eventM) (m.R i w) := by
      intro x hx
      exact hSSub x (intersectWorlds_subset_left S eventM x hx)
    change conditionalize_mu n i w E S = conditionalize_mu m i w E S
    rw [conditionalize_mu_eq_div n E hN i w S]
    rw [conditionalize_mu_eq_div m E hM i w S]
    rw [hEvent]
    have hNumEq := hEq.measure_eq_on_event i w
      (intersectWorlds S eventM) hNumNodup hNumSub
    have hDenEq := hEq.measure_eq_on_event i w eventM hEventNodup hEventSub
    rw [hNumEq, hDenEq]

/-- A finite execution whose every evidence formula lies in the belief-free
static fragment. The constructor stores the admissibility proof required at
each intermediate model. -/
inductive BeliefFreeScheduleRun
    {W Ag Atom : Type} [DecidableEq W] :
    Model W Ag Atom → List (Formula Atom Ag) → Model W Ag Atom → Prop where
  | nil (m : Model W Ag Atom) : BeliefFreeScheduleRun m [] m
  | cons {m out : Model W Ag Atom}
      {E : Formula Atom Ag} {rest : List (Formula Atom Ag)}
      (hFree : E.BeliefFree)
      (hAdm : ConditionalizationAdmissible m E)
      (tail : BeliefFreeScheduleRun (conditionalize m E hAdm) rest out) :
      BeliefFreeScheduleRun m (E :: rest) out

/-- Finite admissible schedules preserve probability integrity. -/
theorem BeliefFreeScheduleRun.preserves_probabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    {m out : Model W Ag Atom} {schedule : List (Formula Atom Ag)}
    (run : BeliefFreeScheduleRun m schedule out)
    (hIntegrity : ModelProbabilityIntegrity m) :
    ModelProbabilityIntegrity out := by
  induction run with
  | nil m => exact hIntegrity
  | @cons m out E rest hFree hAdm tail ih =>
      have hNext := conditionalize_preserves_probabilityIntegrity
        m hIntegrity E hAdm
      exact ih hNext

/-- The same finite belief-free suffix preserves an already established modal
observational equivalence, even when the two executions carry different
admissibility proof objects. -/
theorem beliefFreeScheduleRun_preserves_modalObservationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    {m n outM outN : Model W Ag Atom}
    {schedule : List (Formula Atom Ag)}
    (hEq : ModalObservationEquivalent m n)
    (hIntegrityM : ModelProbabilityIntegrity m)
    (hIntegrityN : ModelProbabilityIntegrity n)
    (runM : BeliefFreeScheduleRun m schedule outM)
    (runN : BeliefFreeScheduleRun n schedule outN) :
    ModalObservationEquivalent outM outN := by
  induction runM generalizing n outN with
  | nil m =>
      cases runN
      exact hEq
  | @cons m out E rest hFree hAdmM tailM ih =>
      cases runN with
      | cons hFreeN hAdmN tailN =>
          have hStepEq :=
            conditionalize_beliefFree_preserves_modalObservationEquivalent
              hEq hIntegrityM E hFree hAdmM hAdmN
          have hNextM := conditionalize_preserves_probabilityIntegrity
            m hIntegrityM E hAdmM
          have hNextN := conditionalize_preserves_probabilityIntegrity
            n hIntegrityN E hAdmN
          exact ih hStepEq hNextM hNextN tailN

/-- The local swap generator for finite schedules. If two complete admissible
runs differ only by reversing two adjacent belief-free updates before a common
suffix, their final models are modally observationally equivalent. -/
theorem beliefFreeSchedule_adjacentSwap_observationEquivalent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (rest : List (Formula Atom Ag))
    (outPQ outQP : Model W Ag Atom)
    (runPQ : BeliefFreeScheduleRun m (P :: Q :: rest) outPQ)
    (runQP : BeliefFreeScheduleRun m (Q :: P :: rest) outQP) :
    ModalObservationEquivalent outPQ outQP := by
  cases runPQ with
  | cons hPFree hP tailPQ =>
      cases tailPQ with
      | cons hQFree hQAfterP suffixPQ =>
          cases runQP with
          | cons hQFree' hQ tailQP =>
              cases tailQP with
              | cons hPFree' hPAfterQ suffixQP =>
                  have hMid :=
                    conditionalize_two_beliefFree_observationEquivalent
                      m hIntegrity P Q hPFree hQFree
                      hP hQ hQAfterP hPAfterQ
                  have hIntP := conditionalize_preserves_probabilityIntegrity
                    m hIntegrity P hP
                  have hIntPQ := conditionalize_preserves_probabilityIntegrity
                    (conditionalize m P hP) hIntP Q hQAfterP
                  have hIntQ := conditionalize_preserves_probabilityIntegrity
                    m hIntegrity Q hQ
                  have hIntQP := conditionalize_preserves_probabilityIntegrity
                    (conditionalize m Q hQ) hIntQ P hPAfterQ
                  exact beliefFreeScheduleRun_preserves_modalObservationEquivalent
                    hMid hIntPQ hIntQP suffixPQ suffixQP

/-- Hence an admissible adjacent swap inside the static fragment cannot change
the final Recovery status of any modal target. -/
theorem beliefFreeSchedule_adjacentSwap_recovery_confluent
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (P Q : Formula Atom Ag)
    (rest : List (Formula Atom Ag))
    (outPQ outQP : Model W Ag Atom)
    (runPQ : BeliefFreeScheduleRun m (P :: Q :: rest) outPQ)
    (runQP : BeliefFreeScheduleRun m (Q :: P :: rest) outQP)
    (phi : ModalFormula Atom Ag) :
    ModalFormula.CompositionalRecovery outPQ phi ↔
      ModalFormula.CompositionalRecovery outQP phi := by
  have hObs := beliefFreeSchedule_adjacentSwap_observationEquivalent
    m hIntegrity P Q rest outPQ outQP runPQ runQP
  have hOutPQ := runPQ.preserves_probabilityIntegrity hIntegrity
  exact (compositionalRecovery_iff_of_modalObservationEquivalent
    hObs hOutPQ phi).symm

end PEL4
