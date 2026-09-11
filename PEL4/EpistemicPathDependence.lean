import PEL4.RecoveryEndpointClassification

namespace PEL4

/-!
# Gate 29: epistemic path dependence

Gate 28 classified the eventual Boolean endpoint of every valid infinite
trajectory but used separate systems to witness eventual Recovery and eventual
Non-Recovery. Gate 29 strengthens the negative result: a *single* descent
system can admit two valid infinite trajectories from the *same* initial state
whose eventual recovery endpoints differ.

This is the minimal formal notion of epistemic path dependence needed before
asking whether concrete 4PEL conditionalization exhibits the same phenomenon.
-/

/-- Recovery endpoint path dependence at a particular initial state. -/
def RecoveryPathDependentAt
    {State : Type} (sys : RecoveryDescentSystem State) (start : State) : Prop :=
  ∃ recoveryPath nonRecoveryPath : Nat -> State,
    recoveryPath 0 = start ∧
    nonRecoveryPath 0 = start ∧
    recoveryTrajectoryFollows sys recoveryPath ∧
    recoveryTrajectoryFollows sys nonRecoveryPath ∧
    EventuallyRecoveryStatus sys recoveryPath true ∧
    EventuallyRecoveryStatus sys nonRecoveryPath false

/-- Stronger future-oriented notion: every valid infinite continuation from the
state eventually remains in Recovery. -/
def RobustEventuallyRecoveryAt
    {State : Type} (sys : RecoveryDescentSystem State) (start : State) : Prop :=
  ∀ trajectory : Nat -> State,
    trajectory 0 = start ->
    recoveryTrajectoryFollows sys trajectory ->
    EventuallyRecoveryStatus sys trajectory true

/-- Three-state minimal witness for Gate 29. -/
inductive Gate29State where
  | start
  | recovery
  | nonRecovery
  deriving DecidableEq, Repr

/-- The initial state and the Recovery branch are currently recovered. -/
def gate29Status : Gate29State -> Bool
  | .start => true
  | .recovery => true
  | .nonRecovery => false

/-- One unit of revision capacity is initially available. Staying on the
Recovery branch leaves it unused; choosing Non-Recovery consumes it. -/
def gate29Potential : Gate29State -> Nat
  | .start => 1
  | .recovery => 1
  | .nonRecovery => 0

/-- The only choice occurs at the start. Afterwards each branch stutters
forever in its own endpoint phase. -/
inductive Gate29Step : Gate29State -> Gate29State -> Prop where
  | chooseRecovery : Gate29Step .start .recovery
  | chooseNonRecovery : Gate29Step .start .nonRecovery
  | stayRecovery : Gate29Step .recovery .recovery
  | stayNonRecovery : Gate29Step .nonRecovery .nonRecovery

/-- A single recovery-descent system containing both asymptotic futures. -/
def gate29System : RecoveryDescentSystem Gate29State where
  status := gate29Status
  potential := gate29Potential
  Step := Gate29Step
  step_budget := by
    intro s t hStep
    cases hStep <;> decide

/-- The future that chooses the Recovery branch at the first step. -/
def gate29RecoveryTrajectory : Nat -> Gate29State
  | 0 => .start
  | _ + 1 => .recovery

/-- The future that chooses the Non-Recovery branch at the first step. -/
def gate29NonRecoveryTrajectory : Nat -> Gate29State
  | 0 => .start
  | _ + 1 => .nonRecovery

@[simp] theorem gate29_recoveryTrajectory_starts_same :
    gate29RecoveryTrajectory 0 = Gate29State.start := rfl

@[simp] theorem gate29_nonRecoveryTrajectory_starts_same :
    gate29NonRecoveryTrajectory 0 = Gate29State.start := rfl

/-- First admissible future: remain recovered forever after the branch. -/
theorem gate29_recoveryTrajectory_follows :
    recoveryTrajectoryFollows gate29System gate29RecoveryTrajectory := by
  intro n
  cases n with
  | zero => exact Gate29Step.chooseRecovery
  | succ n => exact Gate29Step.stayRecovery

/-- Second admissible future from the identical start: spend the single status
change and remain Non-Recovered forever. -/
theorem gate29_nonRecoveryTrajectory_follows :
    recoveryTrajectoryFollows gate29System gate29NonRecoveryTrajectory := by
  intro n
  cases n with
  | zero => exact Gate29Step.chooseNonRecovery
  | succ n => exact Gate29Step.stayNonRecovery

/-- The Recovery branch has the positive asymptotic endpoint. -/
theorem gate29_recoveryTrajectory_eventually_recovery :
    EventuallyRecoveryStatus gate29System gate29RecoveryTrajectory true := by
  refine ⟨1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ k => rfl

/-- The alternative branch has the negative asymptotic endpoint. -/
theorem gate29_nonRecoveryTrajectory_eventually_nonRecovery :
    EventuallyRecoveryStatus gate29System gate29NonRecoveryTrajectory false := by
  refine ⟨1, ?_⟩
  intro n hn
  cases n with
  | zero => omega
  | succ k => rfl

/-- Main Gate-29 witness: same system, same start state, different eventual
Recovery endpoints. -/
theorem gate29_same_start_different_endpoints :
    RecoveryPathDependentAt gate29System Gate29State.start := by
  refine ⟨gate29RecoveryTrajectory, gate29NonRecoveryTrajectory, rfl, rfl,
    gate29_recoveryTrajectory_follows, gate29_nonRecoveryTrajectory_follows,
    gate29_recoveryTrajectory_eventually_recovery,
    gate29_nonRecoveryTrajectory_eventually_nonRecovery⟩

/-- The shared initial state is recovered *now*. -/
theorem gate29_start_is_recovered_now :
    gate29System.status Gate29State.start = true := rfl

/-- Current Recovery does not imply robust eventual Recovery across all
admissible futures. -/
theorem gate29_recovery_now_not_robust_future :
    ¬ RobustEventuallyRecoveryAt gate29System Gate29State.start := by
  intro hRobust
  have hTrue := hRobust gate29NonRecoveryTrajectory rfl
    gate29_nonRecoveryTrajectory_follows
  exact eventuallyRecoveryStatus_exclusive gate29System
    gate29NonRecoveryTrajectory hTrue
    gate29_nonRecoveryTrajectory_eventually_nonRecovery

/-- The two admissible futures are genuinely distinct immediately after the
shared initial state. -/
theorem gate29_paths_diverge_after_start :
    gate29RecoveryTrajectory 1 ≠ gate29NonRecoveryTrajectory 1 := by
  decide

end PEL4
