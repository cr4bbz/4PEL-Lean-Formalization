import PEL4.EpistemicRepairDynamics

namespace PEL4

/-!
# Gate 109: self-correction liveness

Gate 108 verified local repairs for concrete `N` and `B` witnesses. Gate 109 asks
a controller-level question: if every nonclassical coordinate can in fact be
repaired when selected, does the nested epistemic system necessarily return to a
region where both world and model coordinates are classical?

The finite repair controller preserves Gate 104's second-order priority: repair
the model coordinate before the world coordinate. Classical `T/F` coordinates are
left unchanged; a nonclassical `N/B` coordinate is idealistically repaired to `T`.
This is intentionally a liveness baseline. Gate 110 will remove the assumption
that every requested repair is informationally possible.
-/

/-- A coordinate is repair-stable when it is strictly classical. -/
def gate109Classical (value : FDEValue) : Prop :=
  value = FDEValue.T ∨ value = FDEValue.F

/-- `gate109Classical` is decidable because `FDEValue` has decidable equality. -/
instance gate109ClassicalDecidable (value : FDEValue) :
    Decidable (gate109Classical value) := by
  unfold gate109Classical
  infer_instance

/-- Ideal successful repair of one four-valued coordinate. -/
def gate109RepairValue (value : FDEValue) : FDEValue :=
  if gate109Classical value then value else FDEValue.T

/-- The nested state is stable when both epistemic layers are classical. -/
def gate109Stable (state : Gate103NestedStatus) : Prop :=
  gate109Classical state.world ∧ gate109Classical state.model

/-- Count the remaining nonclassical coordinates. The rank is always 0, 1, or 2. -/
def gate109DefectCount (state : Gate103NestedStatus) : Nat :=
  (if gate109Classical state.world then 0 else 1) +
    (if gate109Classical state.model then 0 else 1)

/-- Repair policy: second-order model defects have priority over first-order world
defects, mirroring Gate 104's self-trust discipline. -/
def gate109RepairStep (state : Gate103NestedStatus) : Gate103NestedStatus :=
  if gate109Classical state.model then
    if gate109Classical state.world then
      state
    else
      { state with world := gate109RepairValue state.world }
  else
    { state with model := gate109RepairValue state.model }

/-- Strict truth is a repair-stable coordinate. -/
theorem gate109_T_is_classical : gate109Classical FDEValue.T := by
  exact Or.inl rfl

/-- Ideal repair always produces a classical coordinate. -/
theorem gate109_repair_value_is_classical (value : FDEValue) :
    gate109Classical (gate109RepairValue value) := by
  by_cases h : gate109Classical value
  · simpa [gate109RepairValue, h] using h
  · simpa [gate109RepairValue, h] using gate109_T_is_classical

/-- The defect rank of every nested state is bounded by two. -/
theorem gate109_defect_count_bounded (state : Gate103NestedStatus) :
    gate109DefectCount state ≤ 2 := by
  by_cases hw : gate109Classical state.world
  · by_cases hm : gate109Classical state.model
    · simp [gate109DefectCount, hw, hm]
    · simp [gate109DefectCount, hw, hm]
  · by_cases hm : gate109Classical state.model
    · simp [gate109DefectCount, hw, hm]
    · simp [gate109DefectCount, hw, hm]

/-- Whenever the state is not stable, one repair step strictly decreases the
number of remaining nonclassical coordinates. -/
theorem gate109_unstable_step_strictly_decreases_defects
    (state : Gate103NestedStatus) :
    ¬ gate109Stable state →
      gate109DefectCount (gate109RepairStep state) < gate109DefectCount state := by
  intro hUnstable
  by_cases hm : gate109Classical state.model
  · by_cases hw : gate109Classical state.world
    · exact False.elim (hUnstable ⟨hw, hm⟩)
    · simp [gate109RepairStep, gate109RepairValue, gate109DefectCount,
        hm, hw, gate109_T_is_classical]
  · by_cases hw : gate109Classical state.world
    · simp [gate109RepairStep, gate109RepairValue, gate109DefectCount,
        hm, hw, gate109_T_is_classical]
    · simp [gate109RepairStep, gate109RepairValue, gate109DefectCount,
        hm, hw, gate109_T_is_classical]

/-- Stable states are fixed points of the repair controller. -/
theorem gate109_stable_state_is_fixed_point
    (state : Gate103NestedStatus) :
    gate109Stable state → gate109RepairStep state = state := by
  intro hStable
  rcases hStable with ⟨hw, hm⟩
  simp [gate109RepairStep, hm, hw]

/-- Because there are only two coordinates and every successful repair removes
one defect, two repair steps suffice from every one of the sixteen nested states. -/
theorem gate109_two_steps_reach_stable
    (state : Gate103NestedStatus) :
    gate109Stable (gate109RepairStep (gate109RepairStep state)) := by
  by_cases hm : gate109Classical state.model
  · by_cases hw : gate109Classical state.world
    · simpa [gate109RepairStep, hm, hw, gate109Stable] using And.intro hw hm
    · simp [gate109RepairStep, gate109RepairValue, gate109Stable,
        hm, hw, gate109_T_is_classical]
  · by_cases hw : gate109Classical state.world
    · simp [gate109RepairStep, gate109RepairValue, gate109Stable,
        hm, hw, gate109_T_is_classical]
    · simp [gate109RepairStep, gate109RepairValue, gate109Stable,
        hm, hw, gate109_T_is_classical]

/-- The explicit Gate-103 worst case with a model conflict is repaired before the
already-classical world coordinate is touched. -/
theorem gate109_model_conflict_repairs_first :
    gate109RepairStep gate103TruthWithModelConflict = gate103TrustedTruth := by
  native_decide

/-- A trusted model with a world gap instead repairs the first-order coordinate. -/
theorem gate109_world_gap_repairs_when_model_stable :
    gate109RepairStep gate103WorldGapTrustedModel = gate103TrustedTruth := by
  native_decide

/-- Main Gate-109 liveness theorem: under the ideal repair-success assumption,
the priority controller admits a natural-number ranking that strictly descends on
every unstable step and reaches a stable classical region within two repairs. -/
theorem gate109_self_correction_liveness :
    (∀ state : Gate103NestedStatus,
      gate109DefectCount state ≤ 2) ∧
    (∀ state : Gate103NestedStatus,
      ¬ gate109Stable state →
        gate109DefectCount (gate109RepairStep state) < gate109DefectCount state) ∧
    (∀ state : Gate103NestedStatus,
      gate109Stable (gate109RepairStep (gate109RepairStep state))) := by
  exact ⟨gate109_defect_count_bounded,
    gate109_unstable_step_strictly_decreases_defects,
    gate109_two_steps_reach_stable⟩

/-!
## Gate-109 interpretation boundary

The liveness theorem is conditional on a deliberately strong repair oracle:
whenever `N` or `B` is selected, `gate109RepairValue` can install a classical
verdict. Gate 109 therefore proves termination of a repair architecture, not that
reality always supplies enough information to make the requested repair possible.

That missing premise is now explicit rather than hidden. Gate 110 will attack it:
observationally equivalent states can disagree about the target truth, so no
repair policy restricted to the available evidence channel can be guaranteed to
classify both correctly. The failure mode is informational, not computational.
-/

end PEL4
