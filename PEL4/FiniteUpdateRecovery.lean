import PEL4.ConditionalizationProbabilityIntegrity
import PEL4.ConvexModelPath

namespace PEL4

/-!
# Gate 19: compositional recovery along finite update traces

An admissible evidence formula for a later update depends on the model produced
by every earlier update. The trace type below therefore stores evidence and its
admissibility proof dependently, rather than representing a run as an ordinary
list of formulas.

The gate proves an exact preservation theorem for traces that begin recovered,
isolates the first directed gap in a failing trace, and supplies a concrete
two-step `T -> N -> T` witness showing that recovery can return after it has
been lost.
-/

/-- A finite sequence of admissible conditionalizations of a strong model.
Every tail is indexed by the model produced by the preceding step. -/
inductive FiniteConditionalizationTrace
    {W Ag Atom : Type} [DecidableEq W] :
    StrongProbabilityModel W Ag Atom -> Type where
  | nil (m : StrongProbabilityModel W Ag Atom) :
      FiniteConditionalizationTrace m
  | step (m : StrongProbabilityModel W Ag Atom)
      (E : Formula Atom Ag)
      (hAdm : ConditionalizationAdmissible m.toModel E)
      (tail : FiniteConditionalizationTrace
        (conditionalizeStrong m E hAdm)) :
      FiniteConditionalizationTrace m

namespace FiniteConditionalizationTrace

/-- Number of update edges in a finite trace. -/
def length
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom} :
    FiniteConditionalizationTrace m -> Nat
  | .nil _ => 0
  | .step _ _ _ tail => tail.length + 1

/-- Strong model reached after all updates in the trace. -/
def finalModel
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom} :
    FiniteConditionalizationTrace m -> StrongProbabilityModel W Ag Atom
  | .nil _ => m
  | .step _ _ _ tail => tail.finalModel

/-- Every posterior state in the trace satisfies compositional recovery.
The initial state is supplied separately to the main theorem. -/
def RecoveryPreservedAlong
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (phi : ModalFormula Atom Ag) :
    FiniteConditionalizationTrace m -> Prop
  | .nil _ => True
  | .step m E hAdm tail =>
      ModalFormula.CompositionalRecovery
          (conditionalize m.toModel E hAdm) phi ∧
        RecoveryPreservedAlong phi tail

/-- Every edge in the trace avoids a directed gap at every belief node
reachable from `phi`. -/
def NoDirectionalGapAlong
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (phi : ModalFormula Atom Ag) :
    FiniteConditionalizationTrace m -> Prop
  | .nil _ => True
  | .step m E hAdm tail =>
      ModalFormula.NoDirectionalGap m.toModel E hAdm phi ∧
        NoDirectionalGapAlong phi tail

/-- Gate-19 preservation theorem. If the initial state is recovered, recovery
holds at every later state exactly when every update edge avoids the Gate-12
directed gap pattern. -/
theorem recoveryPreservedAlong_iff_noDirectionalGapAlong
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (phi : ModalFormula Atom Ag)
    (hInitial : ModalFormula.CompositionalRecovery m.toModel phi) :
    RecoveryPreservedAlong phi trace ↔
      NoDirectionalGapAlong phi trace := by
  induction trace with
  | nil _ => rfl
  | step m E hAdm tail ih =>
      have hStep :
          ModalFormula.CompositionalRecovery
              (conditionalize m.toModel E hAdm) phi ↔
            ModalFormula.NoDirectionalGap m.toModel E hAdm phi :=
        compositionalRecovery_conditionalize_iff_noDirectionalGap
          m.toModel m.probability_integrity E hAdm phi hInitial
      constructor
      · rintro ⟨hNext, hTail⟩
        exact ⟨hStep.1 hNext, (ih hNext).1 hTail⟩
      · rintro ⟨hNoGap, hTail⟩
        have hNext := hStep.2 hNoGap
        exact ⟨hNext, (ih hNext).2 hTail⟩

/-- Ordered witness for the first failing edge: either the present edge is the
first directed gap, or the present edge is safe and the first gap lies later. -/
def HasFirstDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (phi : ModalFormula Atom Ag) :
    FiniteConditionalizationTrace m -> Prop
  | .nil _ => False
  | .step m E hAdm tail =>
      ¬ ModalFormula.NoDirectionalGap m.toModel E hAdm phi ∨
        (ModalFormula.NoDirectionalGap m.toModel E hAdm phi ∧
          HasFirstDirectionalGap phi tail)

/-- A finite trace violates the all-edges condition exactly when its recursive
ordered search locates a first directed gap. -/
theorem not_noDirectionalGapAlong_iff_hasFirstDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (phi : ModalFormula Atom Ag) :
    ¬ NoDirectionalGapAlong phi trace ↔
      HasFirstDirectionalGap phi trace := by
  induction trace with
  | nil _ =>
      constructor
      · intro h
        exact h trivial
      · intro h
        exact False.elim h
  | step m E hAdm tail ih =>
      change
        (¬ (ModalFormula.NoDirectionalGap m.toModel E hAdm phi ∧
          NoDirectionalGapAlong phi tail)) ↔
        (¬ ModalFormula.NoDirectionalGap m.toModel E hAdm phi ∨
          (ModalFormula.NoDirectionalGap m.toModel E hAdm phi ∧
            HasFirstDirectionalGap phi tail))
      by_cases hHere : ModalFormula.NoDirectionalGap m.toModel E hAdm phi
      · constructor
        · intro hFailure
          right
          refine ⟨hHere, ih.1 ?_⟩
          intro hTail
          exact hFailure ⟨hHere, hTail⟩
        · rintro (_ | ⟨_, hFirstTail⟩)
          · contradiction
          · intro hAll
            exact (ih.2 hFirstTail) hAll.2
      · constructor
        · intro _
          exact Or.inl hHere
        · intro _ hAll
          exact hHere hAll.1

/-- Starting from recovery, failure to remain recovered has an exact earliest
directed-gap witness in the finite trace. -/
theorem not_recoveryPreservedAlong_iff_hasFirstDirectionalGap
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (phi : ModalFormula Atom Ag)
    (hInitial : ModalFormula.CompositionalRecovery m.toModel phi) :
    ¬ RecoveryPreservedAlong phi trace ↔
      HasFirstDirectionalGap phi trace := by
  rw [not_congr
    (recoveryPreservedAlong_iff_noDirectionalGapAlong trace phi hInitial)]
  exact not_noDirectionalGapAlong_iff_hasFirstDirectionalGap trace phi

/-- Somewhere along the trace, one update moves `phi` from non-recovery back
to recovery. This predicate does not assume that recovery is monotone. -/
def HasRecoveryReturn
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (phi : ModalFormula Atom Ag) :
    FiniteConditionalizationTrace m -> Prop
  | .nil _ => False
  | .step m E hAdm tail =>
      (¬ ModalFormula.CompositionalRecovery m.toModel phi ∧
        ModalFormula.CompositionalRecovery
          (conditionalize m.toModel E hAdm) phi) ∨
      HasRecoveryReturn phi tail

/-- Semantic condition for a single recovery return: recovery is absent before
the edge, while recursive semantic classicality holds in its target model. -/
def RecoveryReturnCondition
    {W Ag Atom : Type} [DecidableEq W]
    (m : StrongProbabilityModel W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m.toModel E)
    (phi : ModalFormula Atom Ag) : Prop :=
  ¬ ModalFormula.CompositionalRecovery m.toModel phi ∧
    ModalFormula.CompositionallyClassical
      (conditionalize m.toModel E hAdm) phi

/-- The semantic target condition is necessary and sufficient for one update
edge to restore recovery. Posterior probability integrity is inherited from the
strong source model. -/
theorem recoveryReturn_iff_condition
    {W Ag Atom : Type} [DecidableEq W]
    (m : StrongProbabilityModel W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m.toModel E)
    (phi : ModalFormula Atom Ag) :
    (¬ ModalFormula.CompositionalRecovery m.toModel phi ∧
      ModalFormula.CompositionalRecovery
        (conditionalize m.toModel E hAdm) phi) ↔
      RecoveryReturnCondition m E hAdm phi := by
  unfold RecoveryReturnCondition
  rw [compositionalRecovery_iff_compositionallyClassical
    (conditionalize m.toModel E hAdm)
    (conditionalize_preserves_probabilityIntegrity
      m.toModel m.probability_integrity E hAdm) phi]

/-- A semantic return condition occurs on some ordered edge of the trace. -/
def HasRecoveryReturnCondition
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (phi : ModalFormula Atom Ag) :
    FiniteConditionalizationTrace m -> Prop
  | .nil _ => False
  | .step m E hAdm tail =>
      RecoveryReturnCondition m E hAdm phi ∨
        HasRecoveryReturnCondition phi tail

/-- Recovery returns somewhere in a finite trace exactly when the corresponding
semantic target condition occurs on some edge. -/
theorem hasRecoveryReturn_iff_hasRecoveryReturnCondition
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (phi : ModalFormula Atom Ag) :
    HasRecoveryReturn phi trace ↔
      HasRecoveryReturnCondition phi trace := by
  induction trace with
  | nil _ => rfl
  | step m E hAdm tail ih =>
      constructor
      · rintro (hHere | hLater)
        · exact Or.inl ((recoveryReturn_iff_condition m E hAdm phi).1 hHere)
        · exact Or.inr (ih.1 hLater)
      · rintro (hHere | hLater)
        · exact Or.inl ((recoveryReturn_iff_condition m E hAdm phi).2 hHere)
        · exact Or.inr (ih.2 hLater)

end FiniteConditionalizationTrace

/-! ## A two-step loss-and-return witness -/

inductive Gate19Atom where
  | p | q | r
  deriving DecidableEq

inductive Gate19World where
  | a | b | c | d
  deriving DecidableEq

def gate19Support : FiniteSet Gate19World := [.a, .b, .c, .d]

def gate19Weight : Gate19World -> Rat
  | .a => 3 / 10
  | .b => 4 / 10
  | .c => 2 / 10
  | .d => 1 / 10

def gate19Val (w : Gate19World) : Gate19Atom -> FDEValue
  | .p => if w = .a ∨ w = .b then FDEValue.T else FDEValue.F
  | .q => if w = .a ∨ w = .c then FDEValue.T else FDEValue.F
  | .r => if w = .a then FDEValue.T else FDEValue.F

theorem gate19WeightDistribution :
    FiniteWeightDistribution gate19Support gate19Weight := by
  refine
    { support_nodup := by decide +kernel
      nonnegative := ?_
      total := by decide +kernel }
  intro w _
  cases w <;> decide +kernel

def gate19StrongModel :
    StrongProbabilityModel Gate19World Unit Gate19Atom :=
  strongWeightGeneratedModel
    gate19Support
    (fun _ _ => gate19Support)
    (fun _ _ => gate19Weight)
    gate19Val
    (fun _ => 2 / 3)
    (fun _ _ => gate19WeightDistribution)
    (by intro _; decide +kernel)
    (by intro _; decide +kernel)

def gate19EvidenceQ : Formula Gate19Atom Unit := .prop .q
def gate19EvidenceR : Formula Gate19Atom Unit := .prop .r
def gate19BelP : ModalFormula Gate19Atom Unit := .bel () (.prop .p)

theorem gate19EvidenceQ_admissible :
    ConditionalizationAdmissible
      gate19StrongModel.toModel gate19EvidenceQ := by
  refine { positive_mass := ?_, mu_total := ?_, mu_empty := ?_ }
  all_goals intro i w; cases i; cases w <;> decide +kernel

def gate19AfterQ :
    StrongProbabilityModel Gate19World Unit Gate19Atom :=
  conditionalizeStrong gate19StrongModel gate19EvidenceQ
    gate19EvidenceQ_admissible

theorem gate19EvidenceR_afterQ_admissible :
    ConditionalizationAdmissible gate19AfterQ.toModel gate19EvidenceR := by
  refine { positive_mass := ?_, mu_total := ?_, mu_empty := ?_ }
  all_goals intro i w; cases i; cases w <;> decide +kernel

def gate19AfterQR :
    StrongProbabilityModel Gate19World Unit Gate19Atom :=
  conditionalizeStrong gate19AfterQ gate19EvidenceR
    gate19EvidenceR_afterQ_admissible

def gate19LossReturnTrace :
    FiniteConditionalizationTrace gate19StrongModel :=
  .step gate19StrongModel gate19EvidenceQ gate19EvidenceQ_admissible
    (.step gate19AfterQ gate19EvidenceR
      gate19EvidenceR_afterQ_admissible (.nil gate19AfterQR))

theorem gate19_loss_return_profile :
    (∀ w, evalModal gate19StrongModel.toModel w gate19BelP = FDEValue.T) ∧
    (∀ w, evalModal gate19AfterQ.toModel w gate19BelP = FDEValue.N) ∧
    (∀ w, evalModal gate19AfterQR.toModel w gate19BelP = FDEValue.T) := by
  constructor
  · intro w; cases w <;> decide +kernel
  constructor
  · intro w; cases w <;> decide +kernel
  · intro w; cases w <;> decide +kernel

theorem gate19_belP_recovered_initially :
    ModalFormula.CompositionalRecovery gate19StrongModel.toModel gate19BelP := by
  intro w
  constructor
  · intro u _
    change IsClassicalValue (gate19Val u Gate19Atom.p)
    cases u
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  · exact beliefThresholdComplete_of_evalModal_bel_eq_T
      gate19StrongModel.toModel () w (.prop .p)
      (gate19_loss_return_profile.1 w)

theorem gate19_belP_not_recovered_after_first_update :
    ¬ ModalFormula.CompositionalRecovery gate19AfterQ.toModel gate19BelP := by
  intro h
  have hGap := gate19_loss_return_profile.2.1 Gate19World.a
  have hComplete := (h Gate19World.a).2
  exact (not_beliefThresholdComplete_of_evalModal_bel_eq_N
    gate19AfterQ.toModel () Gate19World.a (.prop .p) hGap) hComplete

theorem gate19_belP_recovered_after_second_update :
    ModalFormula.CompositionalRecovery gate19AfterQR.toModel gate19BelP := by
  intro w
  constructor
  · intro u _
    change IsClassicalValue (gate19Val u Gate19Atom.p)
    cases u
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  · exact beliefThresholdComplete_of_evalModal_bel_eq_T
      gate19AfterQR.toModel () w (.prop .p)
      (gate19_loss_return_profile.2.2 w)

/-- One finite admissible trace first loses and later regains compositional
recovery. Hence endpoint recovery does not imply recovery throughout. -/
theorem gate19_finite_trace_loses_then_restores :
    ¬ FiniteConditionalizationTrace.RecoveryPreservedAlong
        gate19BelP gate19LossReturnTrace ∧
      FiniteConditionalizationTrace.HasFirstDirectionalGap
        gate19BelP gate19LossReturnTrace ∧
      FiniteConditionalizationTrace.HasRecoveryReturn
        gate19BelP gate19LossReturnTrace ∧
      ModalFormula.CompositionalRecovery
        (FiniteConditionalizationTrace.finalModel gate19LossReturnTrace).toModel
        gate19BelP := by
  have hNotPreserved :
      ¬ FiniteConditionalizationTrace.RecoveryPreservedAlong
        gate19BelP gate19LossReturnTrace := by
    intro h
    exact gate19_belP_not_recovered_after_first_update h.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hNotPreserved
  · exact
      (FiniteConditionalizationTrace.not_recoveryPreservedAlong_iff_hasFirstDirectionalGap
          gate19LossReturnTrace gate19BelP
          gate19_belP_recovered_initially).1 hNotPreserved
  · change
      (¬ ModalFormula.CompositionalRecovery
          gate19StrongModel.toModel gate19BelP ∧
        ModalFormula.CompositionalRecovery gate19AfterQ.toModel gate19BelP) ∨
      ((¬ ModalFormula.CompositionalRecovery
          gate19AfterQ.toModel gate19BelP ∧
        ModalFormula.CompositionalRecovery gate19AfterQR.toModel gate19BelP) ∨
        False)
    exact Or.inr (Or.inl
      ⟨gate19_belP_not_recovered_after_first_update,
        gate19_belP_recovered_after_second_update⟩)
  · change ModalFormula.CompositionalRecovery
      gate19AfterQR.toModel gate19BelP
    exact gate19_belP_recovered_after_second_update

end PEL4
