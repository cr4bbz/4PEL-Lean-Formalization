import PEL4.FourValuedSufficiencyChallenge
import PEL4.EpistemicSelfDoubtBridge

namespace PEL4

/-!
# Gate 108: epistemic repair dynamics

Gate 107 showed that the qualitative nested 4PEL status cannot universally replace
the quantitative belief state for control. Gate 108 therefore keeps both layers:
`T/F/B/N` identifies the *kind* of epistemic defect, while a simple quantitative
potential tracks whether the concrete repair witnesses actually reduce unresolved
joint support.

For the finite witnesses inherited from Gates 77, 80, and 85, define epistemic
tension as the product of positive and negative support. This is not proposed as
a universal uncertainty measure; it is a compact potential that is high when both
channels remain simultaneously substantial in these examples.
-/

/-- Concrete quantitative repair potential used in Gate 108. -/
def gate108Tension (state : Gate77EvidenceState) : Rat :=
  state.posSupport * state.negSupport

/-- The self-doubt gap from Gate 80 carries tension `6/25`. -/
theorem gate108_gap_tension :
    gate108Tension gate80CalibratedEvidence = (6 : Rat) / 25 := by
  native_decide

/-- Either Gate-85 calibration outcome leaves only `9/100` tension. -/
theorem gate108_gap_repair_tension
    (outcome : Gate85CalibrationOutcome) :
    gate108Tension (gate85ResolvedEvidence outcome) = (9 : Rat) / 100 := by
  cases outcome <;> native_decide

/-- Every concrete self-doubt repair strictly lowers the quantitative potential. -/
theorem gate108_gap_repair_strictly_decreases_tension
    (outcome : Gate85CalibrationOutcome) :
    gate108Tension (gate85ResolvedEvidence outcome) <
      gate108Tension gate80CalibratedEvidence := by
  cases outcome <;> native_decide

/-- The contradictory Gate-77 state has substantially larger simultaneous support. -/
theorem gate108_conflict_tension :
    gate108Tension gate77ConflictState = (16 : Rat) / 25 := by
  native_decide

/-- Either contradiction-resolution outcome leaves `9/100` tension. -/
theorem gate108_conflict_repair_tension
    (observation : Gate77ResolutionObservation) :
    gate108Tension (gate77ResolvedState observation) = (9 : Rat) / 100 := by
  cases observation <;> native_decide

/-- Every concrete contradiction repair strictly lowers the same potential. -/
theorem gate108_conflict_repair_strictly_decreases_tension
    (observation : Gate77ResolutionObservation) :
    gate108Tension (gate77ResolvedState observation) <
      gate108Tension gate77ConflictState := by
  cases observation <;> native_decide

/-- The qualitative layer still records which kind of defect is being repaired. -/
theorem gate108_repairs_start_from_distinct_nonclassical_statuses :
    gate77Status gate80CalibratedEvidence = FDEValue.N ∧
    gate77Status gate77ConflictState = FDEValue.B := by
  exact ⟨gate80_calibrated_status_gap, gate77_initial_state_is_glut⟩

/-- Both repair families exit their nonclassical starting point into a strict
classical `T` or `F` status. -/
theorem gate108_repairs_end_classically :
    (∀ outcome : Gate85CalibrationOutcome,
      gate77Status (gate85ResolvedEvidence outcome) = FDEValue.T ∨
      gate77Status (gate85ResolvedEvidence outcome) = FDEValue.F) ∧
    (∀ observation : Gate77ResolutionObservation,
      gate77Status (gate77ResolvedState observation) = FDEValue.T ∨
      gate77Status (gate77ResolvedState observation) = FDEValue.F) := by
  exact ⟨gate85_calibration_resolves_self_doubt,
    gate77_resolution_always_classical⟩

/-- Main Gate-108 result: in two different nonclassical regimes, the existing
repair dynamics both reach strict classical status and strictly reduce one shared
quantitative potential. -/
theorem gate108_epistemic_repair_dynamics :
    gate77Status gate80CalibratedEvidence = FDEValue.N ∧
    gate77Status gate77ConflictState = FDEValue.B ∧
    (∀ outcome : Gate85CalibrationOutcome,
      gate108Tension (gate85ResolvedEvidence outcome) <
        gate108Tension gate80CalibratedEvidence) ∧
    (∀ observation : Gate77ResolutionObservation,
      gate108Tension (gate77ResolvedState observation) <
        gate108Tension gate77ConflictState) ∧
    (∀ outcome : Gate85CalibrationOutcome,
      gate77Status (gate85ResolvedEvidence outcome) = FDEValue.T ∨
      gate77Status (gate85ResolvedEvidence outcome) = FDEValue.F) ∧
    (∀ observation : Gate77ResolutionObservation,
      gate77Status (gate77ResolvedState observation) = FDEValue.T ∨
      gate77Status (gate77ResolvedState observation) = FDEValue.F) := by
  exact ⟨gate80_calibrated_status_gap,
    gate77_initial_state_is_glut,
    gate108_gap_repair_strictly_decreases_tension,
    gate108_conflict_repair_strictly_decreases_tension,
    gate85_calibration_resolves_self_doubt,
    gate77_resolution_always_classical⟩

/-!
## Gate-108 interpretation boundary

`posSupport * negSupport` is a deliberately local potential, not a universal
measure of epistemic quality. In particular, low product alone does not imply
truth, calibration, or even a classical status for arbitrary independent support
states. What Gate 108 establishes is narrower and useful for dynamics: the two
previously verified repair mechanisms admit one quantitative quantity that
strictly decreases on every listed repair outcome while 4PEL separately records
whether the starting defect is a gap `N` or a glut `B`.

Gate 109 can now replace these one-step witnesses with a controller-level liveness
question: if nonclassical coordinates are repeatedly selected for repair, does the
nested epistemic state reach a repair-stable classical region in bounded time?
-/

end PEL4
