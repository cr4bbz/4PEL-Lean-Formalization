import PEL4.ContradictoryModelEvidence
import PEL4.ActiveContradictionResolution

namespace PEL4

/-!
# Gate 103: nested four-valued epistemics

Gate 102 showed that the epistemic model itself may occupy `T`, `F`, `B`, or `N`.
Gate 103 pairs that second-order status with an independent four-valued status of
the world. The resulting product state distinguishes uncertainty or contradiction
about reality from uncertainty or contradiction about the machinery by which the
agent observes reality.
-/

structure Gate103NestedStatus where
  world : FDEValue
  model : FDEValue
  deriving DecidableEq, Repr

/-- Strict world truth with validated model. -/
def gate103TrustedTruth : Gate103NestedStatus :=
  { world := gate77Status gate80NominalEvidence
    model := gate102Status gate102ValidatedEvidence }

/-- The same world status with model-class uncertainty opened by surprise. -/
def gate103TruthWithModelGap : Gate103NestedStatus :=
  { world := gate77Status gate80NominalEvidence
    model := gate101AdequacyStatus (gate101BeliefAfter .anomaly) }

/-- The same world status with contradictory meta-evidence. -/
def gate103TruthWithModelConflict : Gate103NestedStatus :=
  { world := gate77Status gate80NominalEvidence
    model := gate102Status gate102ConflictEvidence }

/-- Inverted calibration changes the world verdict while model status is strict. -/
def gate103ResolvedFalseTrustedModel : Gate103NestedStatus :=
  { world := gate77Status (gate85ResolvedEvidence .inverted)
    model := gate102Status gate102ValidatedEvidence }

/-- First-order contradiction with a trusted epistemic model. -/
def gate103WorldConflictTrustedModel : Gate103NestedStatus :=
  { world := gate77Status gate77ConflictState
    model := gate102Status gate102ValidatedEvidence }

/-- First-order gap with a trusted epistemic model. -/
def gate103WorldGapTrustedModel : Gate103NestedStatus :=
  { world := gate77Status gate80CalibratedEvidence
    model := gate102Status gate102ValidatedEvidence }

theorem gate103_trusted_truth_is_TT :
    gate103TrustedTruth.world = FDEValue.T ∧
    gate103TrustedTruth.model = FDEValue.T := by
  native_decide

theorem gate103_same_world_three_model_statuses :
    gate103TrustedTruth.world = FDEValue.T ∧
    gate103TruthWithModelGap.world = FDEValue.T ∧
    gate103TruthWithModelConflict.world = FDEValue.T ∧
    gate103TrustedTruth.model = FDEValue.T ∧
    gate103TruthWithModelGap.model = FDEValue.N ∧
    gate103TruthWithModelConflict.model = FDEValue.B := by
  native_decide

theorem gate103_same_model_four_world_statuses :
    gate103TrustedTruth.model = FDEValue.T ∧
    gate103ResolvedFalseTrustedModel.model = FDEValue.T ∧
    gate103WorldConflictTrustedModel.model = FDEValue.T ∧
    gate103WorldGapTrustedModel.model = FDEValue.T ∧
    gate103TrustedTruth.world = FDEValue.T ∧
    gate103ResolvedFalseTrustedModel.world = FDEValue.F ∧
    gate103WorldConflictTrustedModel.world = FDEValue.B ∧
    gate103WorldGapTrustedModel.world = FDEValue.N := by
  native_decide

/-- World and model coordinates are extensionally independent in the finite
witness: changing one need not change the other. -/
theorem gate103_coordinates_are_independent_witness :
    gate103TrustedTruth.world = gate103TruthWithModelGap.world ∧
    gate103TrustedTruth.model ≠ gate103TruthWithModelGap.model ∧
    gate103TrustedTruth.model = gate103ResolvedFalseTrustedModel.model ∧
    gate103TrustedTruth.world ≠ gate103ResolvedFalseTrustedModel.world := by
  native_decide

/-- Main Gate-103 theorem: first-order and second-order four-valued status form
separate axes rather than one collapsed epistemic label. -/
theorem gate103_nested_four_valued_epistemics :
    gate103_same_world_three_model_statuses ∧
    gate103_same_model_four_world_statuses ∧
    gate103_coordinates_are_independent_witness := by
  exact ⟨gate103_same_world_three_model_statuses,
    gate103_same_model_four_world_statuses,
    gate103_coordinates_are_independent_witness⟩

/-!
## Gate-103 boundary

Gate 103 establishes product-coordinate independence by explicit witnesses. It
does not claim that every one of the sixteen pairs is reachable under one fixed
dynamical system. Gate 104 will use these nested statuses as inputs to an active
self-trust controller.
-/

end PEL4
