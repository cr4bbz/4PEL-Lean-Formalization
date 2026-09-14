import PEL4.EpistemicRewardAlignment

namespace PEL4

/-!
# Gate 54: truth/calibration bridge for robust Recovery

The earlier decision-theory gates deliberately treated robust Recovery as an
explicit objective without identifying it with correspondence truth. Gate 54
adds the missing bridge in a form that keeps this distinction visible.

A bridge supplies an *external* truth-alignment predicate and a calibration
error. Its key adequacy condition is diagnostic completeness of the stress
suite: whenever a currently recovered state still has positive calibration
error, at least one admitted stress test exposes that error by moving to a
Non-Recovery state. Zero calibration error must in turn entail truth alignment.

Under exactly those bridge assumptions, stress-robust Recovery entails zero
calibration error and therefore truth alignment. Robust Recovery alone still
does not imply truth.
-/

/-- External bridge data connecting Recovery robustness to an independently
specified truth/calibration criterion. -/
structure RecoveryTruthCalibrationBridge (State : Type) where
  Recovered : State -> Prop
  TruthAligned : State -> Prop
  calibrationError : State -> Nat
  Stress : State -> State -> Prop
  /-- Every positive calibration error in a currently recovered state is
  exposed by at least one admitted stress test. -/
  positive_error_exposed :
    ∀ s, Recovered s -> 0 < calibrationError s ->
      ∃ t, Stress s t ∧ ¬ Recovered t
  /-- Perfect calibration is sufficient for the external truth criterion. -/
  zero_error_truth :
    ∀ s, calibrationError s = 0 -> TruthAligned s

/-- Robust Recovery relative to the stress relation carried by a bridge. -/
def BridgeRobustRecovery
    {State : Type}
    (bridge : RecoveryTruthCalibrationBridge State)
    (s : State) : Prop :=
  StressRobustRecovery bridge.Recovered bridge.Stress s

/-- Diagnostic completeness turns robust Recovery into a zero-calibration
certificate. -/
theorem bridgeRobustRecovery_implies_zeroCalibration
    {State : Type}
    (bridge : RecoveryTruthCalibrationBridge State)
    (s : State)
    (hRobust : BridgeRobustRecovery bridge s) :
    bridge.calibrationError s = 0 := by
  cases hError : bridge.calibrationError s with
  | zero =>
      exact hError
  | succ n =>
      have hPositive : 0 < bridge.calibrationError s := by
        simp [hError]
      obtain ⟨t, hStress, hNotRecovered⟩ :=
        bridge.positive_error_exposed s hRobust.1 hPositive
      have hFalse : False := hNotRecovered (hRobust.2 t hStress)
      exact hFalse.elim

/-- Main abstract bridge theorem: robust Recovery is truth-entailing only once
an external calibration criterion and a stress suite complete for remaining
miscalibration have been supplied. -/
theorem bridgeRobustRecovery_implies_truthAligned
    {State : Type}
    (bridge : RecoveryTruthCalibrationBridge State)
    (s : State)
    (hRobust : BridgeRobustRecovery bridge s) :
    bridge.TruthAligned s := by
  apply bridge.zero_error_truth s
  exact bridgeRobustRecovery_implies_zeroCalibration bridge s hRobust

/-! ## Concrete Gate-47/53 witness -/

/-- External correspondence-style target for the finite witness. `start` is
assumed initially aligned and `robust` is the truth-aligned terminal state.
The fragile recovered state is deliberately *not* truth aligned. -/
def gate54TruthAligned : Gate47State -> Prop
  | .start => True
  | .robust => True
  | _ => False

/-- Calibration error for the finite witness. The only zero-error states are
the externally truth-aligned start and robust states. -/
def gate54CalibrationError : Gate47State -> Nat
  | .start => 0
  | .robust => 0
  | _ => 1

/-- Gate-54 bridge on the existing Gate-47 stress relation. The fragile state
has positive calibration error and its admitted stress test exposes that error
by breaking Recovery. -/
def gate54Bridge : RecoveryTruthCalibrationBridge Gate47State where
  Recovered := Gate47Recovered
  TruthAligned := gate54TruthAligned
  calibrationError := gate54CalibrationError
  Stress := Gate47Stress
  positive_error_exposed := by
    intro s hRecovered hPositive
    cases s with
    | start =>
        simp [gate54CalibrationError] at hPositive
    | fragile =>
        refine ⟨.broken, Gate47Stress.fragileBreak, ?_⟩
        simp [Gate47Recovered, gate47Recovered]
    | destabilized =>
        simp [Gate47Recovered, gate47Recovered] at hRecovered
    | integrating =>
        simp [Gate47Recovered, gate47Recovered] at hRecovered
    | robust =>
        simp [gate54CalibrationError] at hPositive
    | broken =>
        simp [Gate47Recovered, gate47Recovered] at hRecovered
  zero_error_truth := by
    intro s hZero
    cases s <;> simp [gate54CalibrationError, gate54TruthAligned] at hZero ⊢

/-- Ordinary Recovery is insufficient for correspondence-style truth even in
the finite witness: the fragile state is recovered but externally misaligned. -/
theorem gate54_recovery_alone_does_not_imply_truth :
    Gate47Recovered .fragile ∧ ¬ gate54TruthAligned .fragile := by
  constructor
  · exact gate47_fragile_is_recovered
  · simp [gate54TruthAligned]

/-- The robust state satisfies the bridge's stress-robust Recovery predicate. -/
theorem gate54_robust_state_is_bridgeRobust :
    BridgeRobustRecovery gate54Bridge .robust := by
  exact gate47_robust_is_robust

/-- The robust state therefore carries a zero-calibration certificate. -/
theorem gate54_robust_state_zero_calibration :
    gate54CalibrationError .robust = 0 := by
  exact bridgeRobustRecovery_implies_zeroCalibration
    gate54Bridge .robust gate54_robust_state_is_bridgeRobust

/-- The desired bridge for the concrete research path: the robust state is
truth aligned, not by definition of Recovery, but via the explicit diagnostic
bridge assumptions. -/
theorem gate54_robust_state_truth_aligned :
    gate54TruthAligned .robust := by
  exact bridgeRobustRecovery_implies_truthAligned
    gate54Bridge .robust gate54_robust_state_is_bridgeRobust

/-- Gate 53's robustness bonus can now be interpreted as targeting a state that
is truth-certified *relative to Gate 54's explicit bridge*. This does not make
all robustness rewards truth rewards in arbitrary models. -/
theorem gate54_gate53_robust_target_is_truth_certified :
    Gate47RobustRecovery .robust ∧ gate54TruthAligned .robust := by
  exact ⟨gate47_robust_is_robust, gate54_robust_state_truth_aligned⟩

/-- Main finite boundary theorem: plain Recovery can coexist with truth
misalignment, while bridge-certified robust Recovery entails zero calibration
error and external truth alignment. -/
theorem gate54_recovery_truth_boundary :
    (Gate47Recovered .fragile ∧ ¬ gate54TruthAligned .fragile) ∧
    (BridgeRobustRecovery gate54Bridge .robust ∧
      gate54CalibrationError .robust = 0 ∧
      gate54TruthAligned .robust) := by
  exact ⟨gate54_recovery_alone_does_not_imply_truth,
    gate54_robust_state_is_bridgeRobust,
    gate54_robust_state_zero_calibration,
    gate54_robust_state_truth_aligned⟩

/-!
## Gate-54 boundary

This gate does **not** prove that robust Recovery is correspondence truth in
4PEL without further assumptions. It proves a conditional bridge theorem:
robust Recovery entails truth alignment when (i) calibration is externally
defined, (ii) every positive residual calibration error in a recovered state is
exposed by an admitted stress test, and (iii) zero calibration error entails the
external truth criterion. These conditions are intentionally explicit so that
future applications can challenge or replace the calibration/stress model
instead of smuggling truth into the definition of Recovery.
-/

end PEL4
