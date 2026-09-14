import PEL4.EpistemicRewardMisspecification
import PEL4.RecoveryUnderSemanticFeedback

namespace PEL4

/-!
# Gate 47: rational destabilization through robust Recovery

Gate 46 showed that a reward which only scores immediate Recovery uniquely
prefers a Recovery-preserving information-acquisition action over a disruptive
probe. Gate 47 asks whether this local ordering can reverse once the objective
cares about *robust* Recovery rather than merely being recovered at the next
step.

The gate deliberately separates two notions:

* `Recovery`: the current status is recovered;
* `StressRobustRecovery`: the current state is recovered and every admitted
  one-step stress test also remains recovered.

The finite witness below has a preserving path which stays immediately
recovered but remains stress-fragile, and a probing path which passes through
temporary Non-Recovery before entering a permanently robust recovered state.
The long-horizon comparison is lexicographic: terminal robust Recovery is
preferred first, and accumulated Recovery is used only as a tie-breaker. This
avoids hiding the result inside an arbitrary large numerical terminal bonus.
-/

/-- Recovery that survives every admitted one-step stress test. -/
def StressRobustRecovery
    {State : Type}
    (Recovered : State -> Prop)
    (Stress : State -> State -> Prop)
    (s : State) : Prop :=
  Recovered s ∧ ∀ t, Stress s t -> Recovered t

/-- Small finite temporal witness used to expose the difference between
immediate and robust epistemic value. -/
inductive Gate47State where
  | start
  | fragile
  | destabilized
  | integrating
  | robust
  | broken
  deriving DecidableEq, Repr

/-- Current Recovery status of the Gate-47 witness. -/
def gate47Recovered : Gate47State -> Bool
  | .start => true
  | .fragile => true
  | .destabilized => false
  | .integrating => false
  | .robust => true
  | .broken => false

/-- Stress tests expose the difference between merely recovered and robustly
recovered states. The fragile state can break; the robust state stays robust. -/
inductive Gate47Stress : Gate47State -> Gate47State -> Prop where
  | fragileBreak : Gate47Stress .fragile .broken
  | robustStay : Gate47Stress .robust .robust

/-- Proposition-valued Recovery predicate for the finite witness. -/
def Gate47Recovered (s : Gate47State) : Prop :=
  gate47Recovered s = true

/-- Stress-stable Recovery for the finite witness. -/
def Gate47RobustRecovery (s : Gate47State) : Prop :=
  StressRobustRecovery Gate47Recovered Gate47Stress s

theorem gate47_fragile_is_recovered : Gate47Recovered .fragile := by
  rfl

theorem gate47_fragile_not_robust : ¬ Gate47RobustRecovery .fragile := by
  intro hRobust
  have hBroken : Gate47Recovered .broken :=
    hRobust.2 .broken Gate47Stress.fragileBreak
  simp [Gate47Recovered, gate47Recovered] at hBroken

theorem gate47_robust_is_robust : Gate47RobustRecovery .robust := by
  constructor
  · rfl
  · intro t hStress
    cases hStress
    rfl

/-- The myopically attractive path: immediate Recovery is preserved forever,
but the state remains stress-fragile. -/
def gate47PreserveTrajectory : Nat -> Gate47State
  | 0 => .start
  | _ => .fragile

/-- The deliberately destabilizing path: two Non-Recovery stages are traversed
before the trajectory enters permanent robust Recovery. -/
def gate47ProbeTrajectory : Nat -> Gate47State
  | 0 => .start
  | 1 => .destabilized
  | 2 => .integrating
  | _ => .robust

/-- One point for being in current Recovery. This is the temporal analogue of
the immediate proxy used by Gate 46. -/
def gate47RecoveryScore (s : Gate47State) : Nat :=
  match gate47Recovered s with
  | true => 1
  | false => 0

/-- Immediate one-step value of a trajectory. -/
def gate47ImmediateValue (trajectory : Nat -> Gate47State) : Nat :=
  gate47RecoveryScore (trajectory 1)

/-- Recovery accumulated over the first three post-choice states. -/
def gate47ThreeStepRecoveryCount (trajectory : Nat -> Gate47State) : Nat :=
  gate47RecoveryScore (trajectory 1) +
    gate47RecoveryScore (trajectory 2) +
    gate47RecoveryScore (trajectory 3)

/-- Computable flag recording whether the horizon endpoint is the verified
robust state. -/
def gate47RobustTerminalFlag (trajectory : Nat -> Gate47State) : Bool :=
  match trajectory 3 with
  | .robust => true
  | _ => false

/-- Long-horizon epistemic value. Robust terminal Recovery is the primary
criterion; accumulated Recovery is retained as a secondary criterion. -/
structure Gate47HorizonValue where
  robustTerminal : Bool
  recoveryCount : Nat
  deriving DecidableEq, Repr

/-- Value of a three-step trajectory. -/
def gate47HorizonValue (trajectory : Nat -> Gate47State) : Gate47HorizonValue where
  robustTerminal := gate47RobustTerminalFlag trajectory
  recoveryCount := gate47ThreeStepRecoveryCount trajectory

/-- Lexicographic comparison: robust terminal Recovery dominates; when both
paths agree on robustness, accumulated Recovery breaks ties. -/
def Gate47LongRunBetter
    (x y : Gate47HorizonValue) : Prop :=
  (x.robustTerminal = true ∧ y.robustTerminal = false) ∨
    (x.robustTerminal = y.robustTerminal ∧ x.recoveryCount > y.recoveryCount)

theorem gate47_preserve_value :
    gate47HorizonValue gate47PreserveTrajectory =
      { robustTerminal := false, recoveryCount := 3 } := by
  rfl

theorem gate47_probe_value :
    gate47HorizonValue gate47ProbeTrajectory =
      { robustTerminal := true, recoveryCount := 1 } := by
  rfl

/-- Gate 46's ordering is reproduced at the immediate horizon: the preserving
path looks strictly better after one step. -/
theorem gate47_preserve_better_immediately :
    gate47ImmediateValue gate47PreserveTrajectory >
      gate47ImmediateValue gate47ProbeTrajectory := by
  decide

/-- At the three-step horizon the ordering reverses because only the probing
path reaches stress-robust Recovery. -/
theorem gate47_probe_better_long_run :
    Gate47LongRunBetter
      (gate47HorizonValue gate47ProbeTrajectory)
      (gate47HorizonValue gate47PreserveTrajectory) := by
  left
  exact ⟨rfl, rfl⟩

/-- The preserve path never becomes robust after the initial decision. -/
theorem gate47_preserve_stays_fragile :
    ∀ n, 1 ≤ n -> ¬ Gate47RobustRecovery (gate47PreserveTrajectory n) := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      change ¬ Gate47RobustRecovery .fragile
      exact gate47_fragile_not_robust

/-- The probing path reaches the robust state at step three and remains there. -/
theorem gate47_probe_eventually_permanent_robust :
    ∀ n, 3 ≤ n -> gate47ProbeTrajectory n = .robust := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero => omega
          | succ n => rfl

/-- Bridge back to Gate 46: the concrete 4PEL one-step proxy still strictly
prefers `preserve` over `probe`. Gate 47 changes the temporal objective, not the
verified Gate-46 fact. -/
theorem gate47_gate46_myopic_order_preserved :
    gate46ImmediateRecoveryReward DynamicInstabilityModel .preserve
        (gate46Outcome .preserve) >
      gate46ImmediateRecoveryReward DynamicInstabilityModel .probe
        (gate46Outcome .probe) := by
  decide

/-- Main Gate-47 theorem: extending the objective from immediate Recovery to
terminal stress-robust Recovery reverses the preference. The disruptive route
is worse locally, passes through Non-Recovery, and is nevertheless the only one
of the two witness trajectories that reaches permanent robust Recovery. -/
theorem gate47_rational_destabilization_preference_reversal :
    gate47ImmediateValue gate47PreserveTrajectory >
        gate47ImmediateValue gate47ProbeTrajectory ∧
    Gate47LongRunBetter
        (gate47HorizonValue gate47ProbeTrajectory)
        (gate47HorizonValue gate47PreserveTrajectory) ∧
    Gate47Recovered .fragile ∧
    ¬ Gate47RobustRecovery .fragile ∧
    ¬ Gate47Recovered .destabilized ∧
    Gate47RobustRecovery .robust ∧
    (∀ n, 3 ≤ n -> gate47ProbeTrajectory n = .robust) := by
  exact ⟨gate47_preserve_better_immediately,
    gate47_probe_better_long_run,
    gate47_fragile_is_recovered,
    gate47_fragile_not_robust,
    by simp [Gate47Recovered, gate47Recovered],
    gate47_robust_is_robust,
    gate47_probe_eventually_permanent_robust⟩

/-!
## Gate-47 boundary

The gate proves a preference reversal relative to an explicitly declared
long-horizon objective that prioritizes stress-robust Recovery. It does not yet
identify robust Recovery with correspondence truth, nor does it claim that all
temporary destabilization is rational. The result is existential and structural:
there are epistemic control problems in which a locally Recovery-damaging move
is selected by a longer-horizon robustness objective.

Gate 48 will turn this one-shot comparison into a repeated control problem and
ask whether exploration is necessary for reaching the robust region.
-/

end PEL4
