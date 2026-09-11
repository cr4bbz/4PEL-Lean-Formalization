import PEL4.RecoveryCausalDescent
import Init.Data.List.Nat.Sum

namespace PEL4

/-!
# Gate 24: finite position-wise budget for recovery-changing edges

Gate 23 assigns every recovery-changing update edge a strict cumulative-scope
loss at a belief position in the finite Gate-21 compiler.  This gate sums the
Gate-20 resources over those positions and derives a trace-length-independent
upper bound on the number of recovery changes.

Compiler duplicates are retained.  They can only enlarge the upper bound, so
coordinate deduplication is a possible sharpening rather than a prerequisite.
-/

/-- Decidable Boolean test for the two classical FDE vertices. -/
def isClassicalValueBool (v : FDEValue) : Bool :=
  (v == FDEValue.T) || (v == FDEValue.F)

theorem isClassicalValueBool_eq_true_iff (v : FDEValue) :
    isClassicalValueBool v = true ↔ IsClassicalValue v := by
  simp [isClassicalValueBool, IsClassicalValue]

/-- Boolean form of recovery on explicit finite roots, computed from the exact
Gate-21 observation compiler. -/
def recoveryStatusOnBool
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
  (phi : ModalFormula Atom Ag) : Bool :=
  (recoveryObservationSitesFrom m roots phi).all
    (fun site => isClassicalValueBool
      (evalModal m site.world site.formula))

/-- The Boolean status is true exactly when compositional recovery holds on
the selected roots. -/
theorem recoveryStatusOnBool_eq_true_iff
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    recoveryStatusOnBool m roots phi = true ↔
      ModalFormula.CompositionalRecoveryOn m roots phi := by
  rw [compositionalRecoveryOn_iff_recoveryObservationSitesFrom
    m hIntegrity roots phi]
  constructor
  · intro hStatus site hSite
    have hAll := List.all_eq_true.mp hStatus site hSite
    exact (isClassicalValueBool_eq_true_iff _).1 hAll
  · intro hRecovery
    apply List.all_eq_true.mpr
    intro site hSite
    exact (isClassicalValueBool_eq_true_iff _).2 (hRecovery site hSite)

/-- Under explicit finite world coverage, the computed status represents the
repository's globally quantified compositional-recovery predicate. -/
theorem recoveryStatusOnBool_eq_true_iff_global_of_covers
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (roots : FiniteSet W)
    (hCovers : WorldListCovers roots)
    (phi : ModalFormula Atom Ag) :
    recoveryStatusOnBool m roots phi = true ↔
      ModalFormula.CompositionalRecovery m phi := by
  exact (recoveryStatusOnBool_eq_true_iff m hIntegrity roots phi).trans
    (compositionalRecoveryOn_iff_global_of_covers m roots phi hCovers)

/-- Two booleans are equal when being true is equivalent for them. -/
theorem Bool.eq_of_eq_true_iff_eq_true
    (a b : Bool)
    (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Length contribution of one compiler position under a supplied cumulative
scope assignment. Non-belief positions carry no probabilistic budget. -/
def recoveryObservationScopeLength
    {W Ag Atom : Type}
    (scope : Ag -> W -> FiniteSet W)
    (site : RecoveryObservationSite W Ag Atom) : Nat :=
  match site.formula with
  | .bel i _ => (scope i site.world).length
  | _ => 0

/-- Indicator that the next evidence update strictly shrinks the cumulative
scope associated with one belief position. -/
def recoveryObservationStrictShrinkIndicator
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (site : RecoveryObservationSite W Ag Atom) : Nat :=
  match site.formula with
  | .bel i _ =>
      if (intersectWorlds (scope i site.world)
          (conditionalizationEvidenceEvent m i site.world E)).length <
          (scope i site.world).length then 1 else 0
  | _ => 0

/-- Scope assignment after intersecting every local cumulative scope with the
next positive-evidence event. -/
def nextRecoveryScope
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) :
    Ag -> W -> FiniteSet W :=
  fun i w => intersectWorlds (scope i w)
    (conditionalizationEvidenceEvent m i w E)

/-- Total current scope potential over all positions in an explicit compiler
list. -/
def recoveryObservationListScopePotential
    {W Ag Atom : Type}
    (sites : FiniteSet (RecoveryObservationSite W Ag Atom))
    (scope : Ag -> W -> FiniteSet W) : Nat :=
  (sites.map (recoveryObservationScopeLength scope)).sum

/-- Total strict-shrink indicators over all positions in an explicit compiler
list at the next edge. -/
def recoveryObservationListStrictShrinkCount
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (sites : FiniteSet (RecoveryObservationSite W Ag Atom))
    (scope : Ag -> W -> FiniteSet W) : Nat :=
  (sites.map
    (recoveryObservationStrictShrinkIndicator m E scope)).sum

/-- Current finite position-wise budget of a formula on finite roots. -/
def recoveryScopePotential
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) : Nat :=
  recoveryObservationListScopePotential
    (recoveryObservationSitesFrom m roots phi) scope

/-- Number of belief positions whose cumulative scope shrinks strictly at the
next edge, counting duplicate compiler positions separately. -/
def recoveryStrictShrinkPositionCount
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) : Nat :=
  recoveryObservationListStrictShrinkCount m E
    (recoveryObservationSitesFrom m roots phi) scope

/-- Every compiler position loses at most its current length potential; a
strict loss pays one unit. -/
theorem recoveryObservation_strictIndicator_add_nextLength_le
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (site : RecoveryObservationSite W Ag Atom) :
    recoveryObservationStrictShrinkIndicator m E scope site +
        recoveryObservationScopeLength (nextRecoveryScope m E scope) site ≤
      recoveryObservationScopeLength scope site := by
  rcases site with ⟨world, formula⟩
  cases formula <;>
    simp only [recoveryObservationStrictShrinkIndicator,
      recoveryObservationScopeLength] <;> try omega
  case bel i body =>
    simp only [nextRecoveryScope]
    split
    · omega
    · simpa using
        FiniteEvidenceScopeDescent.intersectWorlds_length_le
          (scope i world)
          (conditionalizationEvidenceEvent m i world E)

/-- Summed one-edge potential inequality for any finite compiler list. -/
theorem recoveryObservationList_step_budget
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (sites : FiniteSet (RecoveryObservationSite W Ag Atom))
    (scope : Ag -> W -> FiniteSet W) :
    recoveryObservationListStrictShrinkCount m E sites scope +
        recoveryObservationListScopePotential sites
          (nextRecoveryScope m E scope) ≤
      recoveryObservationListScopePotential sites scope := by
  induction sites with
  | nil => simp [recoveryObservationListStrictShrinkCount,
      recoveryObservationListScopePotential]
  | cons site rest ih =>
      have hSite := recoveryObservation_strictIndicator_add_nextLength_le
        m E scope site
      simp only [recoveryObservationListStrictShrinkCount,
        recoveryObservationListScopePotential, List.map_cons, List.sum_cons]
      simp only [recoveryObservationListStrictShrinkCount,
        recoveryObservationListScopePotential] at ih
      omega

/-- A member whose mapped contribution is one makes the whole natural-number
sum at least one. -/
theorem one_le_sum_map_of_mem_eq_one
    {α : Type}
    (xs : List α) (f : α -> Nat) (x : α)
    (hx : x ∈ xs) (hfx : f x = 1) :
    1 ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons head tail ih =>
      rcases List.mem_cons.mp hx with rfl | hxTail
      · simp [hfx]
      · simp only [List.map_cons, List.sum_cons]
        have hTail := ih hxTail
        omega

/-- One recovery-changing edge costs at most the number of strict belief-
position shrinkages occurring on that edge. -/
theorem recoveryChangeIndicator_le_strictShrinkPositionCount
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m i w (scope i w)) :
    (if recoveryStatusOnBool m roots phi =
          recoveryStatusOnBool (conditionalize m E hAdm) roots phi
      then 0 else 1) ≤
      recoveryStrictShrinkPositionCount m E roots phi scope := by
  split
  · simp
  · rename_i hStatusNe
    have hRecoveryChange : ¬
        (ModalFormula.CompositionalRecoveryOn m roots phi ↔
          ModalFormula.CompositionalRecoveryOn
            (conditionalize m E hAdm) roots phi) := by
      intro hRecoveryIff
      apply hStatusNe
      apply Bool.eq_of_eq_true_iff_eq_true
      rw [recoveryStatusOnBool_eq_true_iff m hIntegrity roots phi,
        recoveryStatusOnBool_eq_true_iff
          (conditionalize m E hAdm)
          (conditionalize_preserves_probabilityIntegrity
            m hIntegrity E hAdm) roots phi]
      exact hRecoveryIff
    obtain ⟨site, i, body, hSite, hFormula, hStrict⟩ :=
      recoveryOn_change_has_strictShrink_beliefObservation
        m hIntegrity E hAdm roots phi scope hConcentrated hRecoveryChange
    have hIndicator :
        recoveryObservationStrictShrinkIndicator m E scope site = 1 := by
      rcases site with ⟨world, formula⟩
      dsimp at hFormula hStrict ⊢
      subst formula
      simp [recoveryObservationStrictShrinkIndicator, hStrict]
    unfold recoveryStrictShrinkPositionCount
    unfold recoveryObservationListStrictShrinkCount
    exact one_le_sum_map_of_mem_eq_one
      (recoveryObservationSitesFrom m roots phi)
      (recoveryObservationStrictShrinkIndicator m E scope)
      site hSite hIndicator

/-- At one update edge, strict-shrink occurrences plus the next position-wise
potential do not exceed the current potential. -/
theorem recoveryStrictShrinkPositionCount_add_nextPotential_le
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) :
    recoveryStrictShrinkPositionCount m E roots phi scope +
        recoveryScopePotential (conditionalize m E hAdm) roots phi
          (nextRecoveryScope m E scope) ≤
      recoveryScopePotential m roots phi scope := by
  unfold recoveryStrictShrinkPositionCount recoveryScopePotential
  rw [recoveryObservationSitesFrom_conditionalize]
  exact recoveryObservationList_step_budget m E
    (recoveryObservationSitesFrom m roots phi) scope

/-- Number of edges in a dependent finite update trace at which recovery on
the selected roots changes truth status. -/
def FiniteConditionalizationTrace.recoveryChangeCountOn
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    FiniteConditionalizationTrace m -> Nat
  | .nil _ => 0
  | .step m E hAdm tail =>
      (if recoveryStatusOnBool m.toModel roots phi =
          recoveryStatusOnBool
            (conditionalize m.toModel E hAdm) roots phi
        then 0 else 1) +
      tail.recoveryChangeCountOn roots phi

/-- Cumulative scope assignment remaining after an entire trace, starting
from an arbitrary assignment. -/
def FiniteConditionalizationTrace.finalRecoveryScopeFrom
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (scope : Ag -> W -> FiniteSet W) :
    Ag -> W -> FiniteSet W :=
  fun i w =>
    (trace.evidenceScopeDescentFrom i w (scope i w)).finalScope

/-- Strong Gate-24 resource inequality from an arbitrary concentrated scope
assignment. The unused final potential is retained, strengthening the bare
change-count bound. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_add_finalPotential_le
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m.toModel i w (scope i w)) :
    trace.recoveryChangeCountOn roots phi +
        recoveryScopePotential trace.finalModel.toModel roots phi
          (trace.finalRecoveryScopeFrom scope) ≤
      recoveryScopePotential m.toModel roots phi scope := by
  induction trace generalizing scope with
  | nil m =>
      have hFinalScope :
          (FiniteConditionalizationTrace.nil m).finalRecoveryScopeFrom scope =
            scope := by
        funext i w
        rfl
      rw [hFinalScope]
      change
        0 + recoveryScopePotential m.toModel roots phi scope ≤
          recoveryScopePotential m.toModel roots phi scope
      omega
  | step m E hAdm tail ih =>
      let nextScope := nextRecoveryScope m.toModel E scope
      have hNextConcentrated : ∀ i w,
          LocalMeasureConcentratedOn
            (conditionalize m.toModel E hAdm) i w (nextScope i w) := by
        intro i w
        exact conditionalize_preserves_localMeasureConcentration
          m.toModel m.probability_integrity E hAdm i w
            (scope i w) (hConcentrated i w)
      have hTail := ih nextScope hNextConcentrated
      have hTail' :
          tail.recoveryChangeCountOn roots phi +
              recoveryScopePotential tail.finalModel.toModel roots phi
                (tail.finalRecoveryScopeFrom nextScope) ≤
            recoveryScopePotential
              (conditionalize m.toModel E hAdm) roots phi nextScope := by
        simpa [conditionalizeStrong] using hTail
      have hChangeCost :=
        recoveryChangeIndicator_le_strictShrinkPositionCount
          m.toModel m.probability_integrity E hAdm roots phi
            scope hConcentrated
      have hScopeStep :=
        recoveryStrictShrinkPositionCount_add_nextPotential_le
          m.toModel E hAdm roots phi scope
      have hScopeStep' :
          recoveryStrictShrinkPositionCount m.toModel E roots phi scope +
              recoveryScopePotential
                (conditionalize m.toModel E hAdm) roots phi nextScope ≤
            recoveryScopePotential m.toModel roots phi scope := by
        simpa [nextScope] using hScopeStep
      have hHead :
          (if recoveryStatusOnBool m.toModel roots phi =
                recoveryStatusOnBool
                  (conditionalize m.toModel E hAdm) roots phi
            then 0 else 1) +
              recoveryScopePotential
                (conditionalize m.toModel E hAdm) roots phi nextScope ≤
            recoveryScopePotential m.toModel roots phi scope := by
        omega
      change
        ((if recoveryStatusOnBool m.toModel roots phi =
                recoveryStatusOnBool
                  (conditionalize m.toModel E hAdm) roots phi
            then 0 else 1) + tail.recoveryChangeCountOn roots phi) +
            recoveryScopePotential tail.finalModel.toModel roots phi
              (tail.finalRecoveryScopeFrom nextScope) ≤
          recoveryScopePotential m.toModel roots phi scope
      omega

/-- Initial position-wise scope budget, counting every belief occurrence in
the exact finite Gate-21 compiler. -/
def initialRecoveryScopeBudget
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) : Nat :=
  recoveryScopePotential m roots phi (fun i w => m.R i w)

/-- Strong initial-budget form: recovery changes plus the final remaining
position-wise potential are bounded by the initial compiler budget. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_add_finalPotential_le_initialBudget
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    trace.recoveryChangeCountOn roots phi +
        recoveryScopePotential trace.finalModel.toModel roots phi
          (trace.finalRecoveryScopeFrom
            (fun i w => m.toModel.R i w)) ≤
      initialRecoveryScopeBudget m.toModel roots phi := by
  exact trace.recoveryChangeCountOn_add_finalPotential_le roots phi
    (fun i w => m.toModel.R i w)
    (fun i w => localMeasureConcentratedOn_accessibility
      m.toModel m.probability_integrity i w)

/-- Main Gate-24 numerical theorem. The number of recovery-changing edges in
an arbitrarily long finite admissible trace is bounded independently of trace
length by the initial finite position-wise evidence budget. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_le_initialBudget
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    trace.recoveryChangeCountOn roots phi ≤
      initialRecoveryScopeBudget m.toModel roots phi := by
  have h :=
    trace.recoveryChangeCountOn_add_finalPotential_le_initialBudget roots phi
  omega

/-- Sanity bound: a trace cannot change recovery status more often than it
has update edges. Unlike the Gate-24 budget, this bound grows with the trace. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_le_length
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    trace.recoveryChangeCountOn roots phi ≤ trace.length := by
  induction trace with
  | nil _ => exact Nat.le_refl _
  | step m E hAdm tail ih =>
      simp only [recoveryChangeCountOn,
        FiniteConditionalizationTrace.length]
      split <;> omega

/-- The Gate-19 loss-and-return trace changes recovery status on both edges. -/
theorem gate24_gate19_recoveryChangeCount :
    gate19LossReturnTrace.recoveryChangeCountOn
      gate19Support gate19BelP = 2 := by
  decide +kernel

/-- Its safe position-wise initial budget counts four accessible worlds at
each of the four compiled belief observations. -/
theorem gate24_gate19_initialRecoveryScopeBudget :
    initialRecoveryScopeBudget gate19StrongModel.toModel
      gate19Support gate19BelP = 16 := by
  decide +kernel

/-- Four units remain after the two updates, so the stronger concrete
inequality reads `2 + 4 ≤ 16`. -/
theorem gate24_gate19_finalRecoveryScopePotential :
    recoveryScopePotential gate19LossReturnTrace.finalModel.toModel
        gate19Support gate19BelP
        (gate19LossReturnTrace.finalRecoveryScopeFrom
          (fun i w => gate19StrongModel.toModel.R i w)) = 4 := by
  decide +kernel

/-- Thus the concrete two-change trace is an executable instance of the
trace-length-independent Gate-24 bound. -/
theorem gate24_gate19_recoveryChangeCount_le_initialBudget :
    gate19LossReturnTrace.recoveryChangeCountOn gate19Support gate19BelP ≤
      initialRecoveryScopeBudget gate19StrongModel.toModel
        gate19Support gate19BelP := by
  exact gate19LossReturnTrace.recoveryChangeCountOn_le_initialBudget
    gate19Support gate19BelP

end PEL4
