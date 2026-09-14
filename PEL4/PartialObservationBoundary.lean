import PEL4.TruthCalibrationBridge

namespace PEL4

/-!
# Gate 55: partial-observation boundary

Gate 54 supplied an external truth/calibration bridge for stress-robust
Recovery. Gate 55 now asks whether a controller that sees only the coarse
Recovery/Non-Recovery signal can use that signal as its complete decision
state.

The answer is no, already in the finite Gate-47/48 witness. `fragile` and
`robust` generate the same current observation, yet they differ in calibration,
truth alignment, robustness, and even in the next observation produced by the
same exploratory action. Thus the visible Recovery bit is not a Markov-sufficient
state representation for this controller.
-/

inductive Gate55Observation where
  | recovery
  | nonRecovery
  deriving DecidableEq, Repr

/-- Coarse observation available to the partially observing controller. -/
def gate55Observe : Gate47State -> Gate55Observation
  | .start => .recovery
  | .fragile => .recovery
  | .robust => .recovery
  | .destabilized => .nonRecovery
  | .integrating => .nonRecovery
  | .broken => .nonRecovery

/-- A generic observation map determines a quantity when observation-equivalent
hidden states always agree on that quantity. -/
def ObservationDetermines
    {State Observation Value : Type}
    (observe : State -> Observation)
    (quantity : State -> Value) : Prop :=
  ∀ s t, observe s = observe t -> quantity s = quantity t

/-- Predicate-valued analogue of `ObservationDetermines`. -/
def ObservationDeterminesPredicate
    {State Observation : Type}
    (observe : State -> Observation)
    (property : State -> Prop) : Prop :=
  ∀ s t, observe s = observe t -> (property s ↔ property t)

/-- Deterministic observation-level Markov sufficiency: equal current
observations must yield equal next observations under every common action. -/
def ObservationTransitionSufficient
    {State Action Observation : Type}
    (observe : State -> Observation)
    (transition : State -> Action -> State) : Prop :=
  ∀ s t a,
    observe s = observe t ->
      observe (transition s a) = observe (transition t a)

/-- The fragile and robust hidden states are observationally aliased by the
Recovery bit. -/
theorem gate55_fragile_robust_same_observation :
    gate55Observe .fragile = gate55Observe .robust := by
  rfl

/-- Yet the same two hidden states carry different Gate-54 calibration error. -/
theorem gate55_fragile_robust_different_calibration :
    gate54CalibrationError .fragile ≠ gate54CalibrationError .robust := by
  decide

/-- Consequently, the Recovery observation does not determine calibration. -/
theorem gate55_recovery_observation_not_calibration_sufficient :
    ¬ ObservationDetermines gate55Observe gate54CalibrationError := by
  intro hDetermines
  have hEq := hDetermines .fragile .robust gate55_fragile_robust_same_observation
  simp [gate54CalibrationError] at hEq

/-- The aliased states also disagree on the external Gate-54 truth criterion. -/
theorem gate55_recovery_observation_not_truth_sufficient :
    ¬ ObservationDeterminesPredicate gate55Observe gate54TruthAligned := by
  intro hDetermines
  have hIff := hDetermines .fragile .robust gate55_fragile_robust_same_observation
  have hRobustTruth : gate54TruthAligned .robust :=
    gate54_robust_state_truth_aligned
  have hFragileTruth : gate54TruthAligned .fragile := hIff.mpr hRobustTruth
  exact (gate54_recovery_alone_does_not_imply_truth.2) hFragileTruth

/-- The same visible Recovery signal does not determine stress robustness either. -/
theorem gate55_recovery_observation_not_robustness_sufficient :
    ¬ ObservationDeterminesPredicate gate55Observe Gate47RobustRecovery := by
  intro hDetermines
  have hIff := hDetermines .fragile .robust gate55_fragile_robust_same_observation
  have hFragileRobust : Gate47RobustRecovery .fragile :=
    hIff.mpr gate47_robust_is_robust
  exact gate47_fragile_not_robust hFragileRobust

/-- Under the same action, observationally aliased states can produce different
next observations: exploring from `fragile` destabilizes, while exploring from
`robust` leaves the robust state fixed. -/
theorem gate55_same_observation_same_action_different_next_observation :
    gate55Observe .fragile = gate55Observe .robust ∧
    gate55Observe (gate48Transition .fragile .explore) ≠
      gate55Observe (gate48Transition .robust .explore) := by
  constructor
  · exact gate55_fragile_robust_same_observation
  · decide

/-- Main Gate-55 Markov boundary: the visible Recovery bit is not sufficient to
induce a deterministic Markov state process from the hidden Gate-47 dynamics. -/
theorem gate55_recovery_observation_not_transition_sufficient :
    ¬ ObservationTransitionSufficient gate55Observe gate48Transition := by
  intro hSufficient
  have hNext := hSufficient .fragile .robust .explore
    gate55_fragile_robust_same_observation
  simp [gate55Observe, gate48Transition] at hNext

/-- Consolidated partial-observation witness. One observation class contains
states that differ in calibration, truth, robustness, and next-observation
dynamics. -/
theorem gate55_partial_observation_boundary :
    gate55Observe .fragile = gate55Observe .robust ∧
    gate54CalibrationError .fragile ≠ gate54CalibrationError .robust ∧
    (¬ gate54TruthAligned .fragile ∧ gate54TruthAligned .robust) ∧
    (¬ Gate47RobustRecovery .fragile ∧ Gate47RobustRecovery .robust) ∧
    gate55Observe (gate48Transition .fragile .explore) ≠
      gate55Observe (gate48Transition .robust .explore) := by
  exact ⟨gate55_fragile_robust_same_observation,
    gate55_fragile_robust_different_calibration,
    gate54_recovery_alone_does_not_imply_truth.2,
    gate54_robust_state_truth_aligned,
    gate47_fragile_not_robust,
    gate47_robust_is_robust,
    gate55_same_observation_same_action_different_next_observation.2⟩

/-!
## Gate-55 boundary

Gate 55 proves insufficiency of one specific coarse observation map. It does not
claim that every partial observation scheme fails, nor that a POMDP is the only
possible formalism. The verified point is narrower and stronger than an analogy:
for the existing controlled epistemic dynamics, treating the Recovery bit as a
fully observed Markov state is formally invalid. A hidden-state or belief-state
representation is therefore justified for this observation regime.
-/

end PEL4
