import PEL4.FiniteRecoveryFlipBudget
import Init.Data.List.Nat.Sum

namespace PEL4

/-!
# Gate 25: duplicate-free recovery coordinate budget

Gate 24 counts every belief occurrence in the exact Gate-21 compiler.  Distinct
occurrences can nevertheless inspect the same `(agent, world)` evidence scope.
This gate quotients that positional accounting by the semantic coordinate that
actually owns the finite scope resource.

The implementation keeps one inert `none` key for non-belief observations.
That key always contributes zero potential and zero shrink cost.  Meaningful
keys are `some (i, w)`, and `dedupRecoveryKeys` guarantees that each such
agent/world coordinate is counted only once.
-/

/-- Small repository-local duplicate eliminator.  We avoid adding a library
dependency solely for the quotienting step. -/
def dedupRecoveryKeys {α : Type} [DecidableEq α] : List α -> List α
  | [] => []
  | x :: xs =>
      let rest := dedupRecoveryKeys xs
      if x ∈ rest then rest else x :: rest

/-- Duplicate elimination preserves membership. -/
theorem mem_dedupRecoveryKeys_iff
    {α : Type} [DecidableEq α] (a : α) :
    ∀ xs : List α, a ∈ dedupRecoveryKeys xs ↔ a ∈ xs := by
  intro xs
  induction xs with
  | nil => simp [dedupRecoveryKeys]
  | cons x xs ih =>
      simp only [dedupRecoveryKeys]
      let rest := dedupRecoveryKeys xs
      by_cases hx : x ∈ rest
      · rw [if_pos hx]
        constructor
        · intro ha
          exact List.mem_cons_of_mem x ((ih).1 ha)
        · intro ha
          rcases List.mem_cons.mp ha with hax | hxs
          · subst a
            exact hx
          · exact (ih).2 hxs
      · rw [if_neg hx]
        constructor
        · intro ha
          rcases List.mem_cons.mp ha with hax | hrest
          · exact List.mem_cons.mpr (Or.inl hax)
          · exact List.mem_cons.mpr (Or.inr ((ih).1 hrest))
        · intro ha
          rcases List.mem_cons.mp ha with hax | hxs
          · exact List.mem_cons.mpr (Or.inl hax)
          · exact List.mem_cons.mpr (Or.inr ((ih).2 hxs))

/-- Semantic resource key extracted from a Gate-21 recovery observation.
Atomic observations receive the inert key `none`; belief observations receive
their unique `(agent, world)` coordinate. -/
def recoveryObservationCoordinateKey
    {W Ag Atom : Type}
    (site : RecoveryObservationSite W Ag Atom) : Option (Ag × W) :=
  match site.formula with
  | .bel i _ => some (i, site.world)
  | _ => none

/-- Duplicate-free finite coordinate compiler. -/
def recoveryCoordinateKeysFrom
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) : FiniteSet (Option (Ag × W)) :=
  dedupRecoveryKeys
    ((recoveryObservationSitesFrom m roots phi).map
      recoveryObservationCoordinateKey)

/-- A compiled belief site contributes its semantic coordinate to the
coordinate quotient. -/
theorem recoveryCoordinateKey_mem_of_beliefSite
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (site : RecoveryObservationSite W Ag Atom)
    (i : Ag) (body : ModalFormula Atom Ag)
    (hSite : site ∈ recoveryObservationSitesFrom m roots phi)
    (hFormula : site.formula = ModalFormula.bel i body) :
    some (i, site.world) ∈ recoveryCoordinateKeysFrom m roots phi := by
  unfold recoveryCoordinateKeysFrom
  apply (mem_dedupRecoveryKeys_iff
    (some (i, site.world)) _).2
  apply List.mem_map.mpr
  refine ⟨site, hSite, ?_⟩
  rcases site with ⟨world, formula⟩
  dsimp at hFormula ⊢
  subst formula
  rfl

/-- The coordinate quotient is invariant under probability-only
conditionalization because the exact Gate-21 compiler is invariant. -/
theorem recoveryCoordinateKeysFrom_conditionalize
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    recoveryCoordinateKeysFrom (conditionalize m E hAdm) roots phi =
      recoveryCoordinateKeysFrom m roots phi := by
  unfold recoveryCoordinateKeysFrom
  rw [recoveryObservationSitesFrom_conditionalize]

/-- Current scope length carried by one unique coordinate key. -/
def recoveryCoordinateScopeLength
    {W Ag : Type}
    (scope : Ag -> W -> FiniteSet W) : Option (Ag × W) -> Nat
  | none => 0
  | some (i, w) => (scope i w).length

/-- Indicator that one unique coordinate loses scope strictly on the next
conditionalization edge. -/
def recoveryCoordinateStrictShrinkIndicator
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) : Option (Ag × W) -> Nat
  | none => 0
  | some (i, w) =>
      if (intersectWorlds (scope i w)
          (conditionalizationEvidenceEvent m i w E)).length <
          (scope i w).length then 1 else 0

/-- Duplicate-free scope potential over all unique compiled coordinates. -/
def recoveryCoordinatePotential
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) : Nat :=
  ((recoveryCoordinateKeysFrom m roots phi).map
    (recoveryCoordinateScopeLength scope)).sum

/-- Number of unique compiled coordinates that shrink strictly at one edge. -/
def recoveryStrictShrinkCoordinateCount
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) : Nat :=
  ((recoveryCoordinateKeysFrom m roots phi).map
    (recoveryCoordinateStrictShrinkIndicator m E scope)).sum

/-- At one unique coordinate, a strict loss pays one unit and the remaining
scope cannot exceed the current scope. -/
theorem recoveryCoordinate_strictIndicator_add_nextLength_le
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (key : Option (Ag × W)) :
    recoveryCoordinateStrictShrinkIndicator m E scope key +
        recoveryCoordinateScopeLength (nextRecoveryScope m E scope) key ≤
      recoveryCoordinateScopeLength scope key := by
  cases key with
  | none => simp [recoveryCoordinateStrictShrinkIndicator,
      recoveryCoordinateScopeLength]
  | some coord =>
      rcases coord with ⟨i, w⟩
      simp only [recoveryCoordinateStrictShrinkIndicator,
        recoveryCoordinateScopeLength, nextRecoveryScope]
      split
      · omega
      · simpa using
          FiniteEvidenceScopeDescent.intersectWorlds_length_le
            (scope i w)
            (conditionalizationEvidenceEvent m i w E)

/-- Summing the one-coordinate inequality over any finite key list preserves
the resource bound. -/
theorem recoveryCoordinateList_step_budget
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (keys : FiniteSet (Option (Ag × W)))
    (scope : Ag -> W -> FiniteSet W) :
    (keys.map (recoveryCoordinateStrictShrinkIndicator m E scope)).sum +
        (keys.map
          (recoveryCoordinateScopeLength
            (nextRecoveryScope m E scope))).sum ≤
      (keys.map (recoveryCoordinateScopeLength scope)).sum := by
  induction keys with
  | nil => simp
  | cons key rest ih =>
      have hKey :=
        recoveryCoordinate_strictIndicator_add_nextLength_le
          m E scope key
      simp only [List.map_cons, List.sum_cons]
      omega

/-- A recovery-changing edge consumes at least one unique coordinate resource.
This is the central Gate-25 sharpening of Gate 24. -/
theorem recoveryChangeIndicator_le_strictShrinkCoordinateCount
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
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
      recoveryStrictShrinkCoordinateCount m E roots phi scope := by
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
    have hKey :
        some (i, site.world) ∈ recoveryCoordinateKeysFrom m roots phi :=
      recoveryCoordinateKey_mem_of_beliefSite
        m roots phi site i body hSite hFormula
    have hIndicator :
        recoveryCoordinateStrictShrinkIndicator m E scope
          (some (i, site.world)) = 1 := by
      simp [recoveryCoordinateStrictShrinkIndicator, hStrict]
    unfold recoveryStrictShrinkCoordinateCount
    exact one_le_sum_map_of_mem_eq_one
      (recoveryCoordinateKeysFrom m roots phi)
      (recoveryCoordinateStrictShrinkIndicator m E scope)
      (some (i, site.world)) hKey hIndicator

/-- Unique strict-shrink costs plus the next duplicate-free potential do not
exceed the current duplicate-free potential. -/
theorem recoveryStrictShrinkCoordinateCount_add_nextPotential_le
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) :
    recoveryStrictShrinkCoordinateCount m E roots phi scope +
        recoveryCoordinatePotential (conditionalize m E hAdm) roots phi
          (nextRecoveryScope m E scope) ≤
      recoveryCoordinatePotential m roots phi scope := by
  unfold recoveryStrictShrinkCoordinateCount recoveryCoordinatePotential
  rw [recoveryCoordinateKeysFrom_conditionalize]
  exact recoveryCoordinateList_step_budget m E
    (recoveryCoordinateKeysFrom m roots phi) scope

/-- Direct one-edge descent contract: a recovery status change costs one unit
of duplicate-free coordinate potential. -/
theorem recoveryChangeIndicator_add_nextCoordinatePotential_le
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
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
      then 0 else 1) +
        recoveryCoordinatePotential (conditionalize m E hAdm) roots phi
          (nextRecoveryScope m E scope) ≤
      recoveryCoordinatePotential m roots phi scope := by
  have hChange :=
    recoveryChangeIndicator_le_strictShrinkCoordinateCount
      m hIntegrity E hAdm roots phi scope hConcentrated
  have hScope :=
    recoveryStrictShrinkCoordinateCount_add_nextPotential_le
      m E hAdm roots phi scope
  omega

/-- Strong Gate-25 trace invariant.  Recovery changes already incurred plus
unused final duplicate-free coordinate potential never exceed the initial
coordinate potential. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_add_finalCoordinatePotential_le
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m.toModel i w (scope i w)) :
    trace.recoveryChangeCountOn roots phi +
        recoveryCoordinatePotential trace.finalModel.toModel roots phi
          (trace.finalRecoveryScopeFrom scope) ≤
      recoveryCoordinatePotential m.toModel roots phi scope := by
  induction trace generalizing scope with
  | nil m =>
      have hFinalScope :
          (FiniteConditionalizationTrace.nil m).finalRecoveryScopeFrom scope =
            scope := by
        funext i w
        rfl
      rw [hFinalScope]
      change
        0 + recoveryCoordinatePotential m.toModel roots phi scope ≤
          recoveryCoordinatePotential m.toModel roots phi scope
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
              recoveryCoordinatePotential tail.finalModel.toModel roots phi
                (tail.finalRecoveryScopeFrom nextScope) ≤
            recoveryCoordinatePotential
              (conditionalize m.toModel E hAdm) roots phi nextScope := by
        simpa [conditionalizeStrong] using hTail
      have hHead :=
        recoveryChangeIndicator_add_nextCoordinatePotential_le
          m.toModel m.probability_integrity E hAdm roots phi
            scope hConcentrated
      have hHead' :
          (if recoveryStatusOnBool m.toModel roots phi =
                recoveryStatusOnBool
                  (conditionalize m.toModel E hAdm) roots phi
            then 0 else 1) +
              recoveryCoordinatePotential
                (conditionalize m.toModel E hAdm) roots phi nextScope ≤
            recoveryCoordinatePotential m.toModel roots phi scope := by
        simpa [nextScope] using hHead
      change
        ((if recoveryStatusOnBool m.toModel roots phi =
                recoveryStatusOnBool
                  (conditionalize m.toModel E hAdm) roots phi
            then 0 else 1) + tail.recoveryChangeCountOn roots phi) +
            recoveryCoordinatePotential tail.finalModel.toModel roots phi
              (tail.finalRecoveryScopeFrom nextScope) ≤
          recoveryCoordinatePotential m.toModel roots phi scope
      omega

/-- Initial duplicate-free coordinate budget. -/
def initialRecoveryCoordinateBudget
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) : Nat :=
  recoveryCoordinatePotential m roots phi (fun i w => m.R i w)

/-- Strong initial-budget form of Gate 25. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_add_finalCoordinatePotential_le_initialBudget
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    trace.recoveryChangeCountOn roots phi +
        recoveryCoordinatePotential trace.finalModel.toModel roots phi
          (trace.finalRecoveryScopeFrom
            (fun i w => m.toModel.R i w)) ≤
      initialRecoveryCoordinateBudget m.toModel roots phi := by
  exact trace.recoveryChangeCountOn_add_finalCoordinatePotential_le
    roots phi (fun i w => m.toModel.R i w)
    (fun i w => localMeasureConcentratedOn_accessibility
      m.toModel m.probability_integrity i w)

/-- Main Gate-25 theorem: finite recovery flipping is bounded by the initial
sum over unique reachable belief coordinates, not compiler occurrences. -/
theorem FiniteConditionalizationTrace.recoveryChangeCountOn_le_initialCoordinateBudget
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag) :
    trace.recoveryChangeCountOn roots phi ≤
      initialRecoveryCoordinateBudget m.toModel roots phi := by
  have h :=
    trace.recoveryChangeCountOn_add_finalCoordinatePotential_le_initialBudget
      roots phi
  omega

end PEL4
