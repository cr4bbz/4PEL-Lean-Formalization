import PEL4.RecoveryEndpointClassification
import PEL4.DynamicCompositionalRecovery

namespace PEL4

/-!
# Gate 29: epistemic path dependence

Gate 28 classified the eventual Boolean endpoint of every valid infinite
trajectory but used separate systems to witness eventual Recovery and eventual
Non-Recovery. Gate 29 strengthens the negative result: a *single* descent
system can admit two valid infinite trajectories from the *same* initial state
whose eventual recovery endpoints differ.

The gate has two layers. First, a minimal abstract descent system establishes
same-start asymptotic path dependence. Second, the existing concrete 4PEL
DynamicInstabilityModel is reused to show that two admissible conditionalization
choices from the same recovered model can already split Recovery at one step.
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

/-- Main abstract Gate-29 witness: same system, same start state, different
eventual Recovery endpoints. -/
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

/-! ## Concrete 4PEL conditionalization split -/

/-- Alternative evidence on the same DynamicInstabilityModel. Conditioning on
`p` selects worlds `a,c`, where `p` itself is positive. -/
def gate29RecoveryPreservingEvidence :
    Formula DynamicInstabilityAtom DynamicInstabilityAgent :=
  Formula.prop DynamicInstabilityAtom.p

/-- Conditioning the shared starting model on `p` is admissible at every local
agent/world pair. -/
theorem gate29_recoveryPreservingEvidence_admissible :
    ConditionalizationAdmissible DynamicInstabilityModel
      gate29RecoveryPreservingEvidence := by
  constructor
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel

/-- Recovery-preserving successor reached from exactly the same concrete model
used by the destructive `e` update. -/
def Gate29RecoveryPreservingUpdated :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize DynamicInstabilityModel gate29RecoveryPreservingEvidence
    gate29_recoveryPreservingEvidence_admissible

/-- After learning `p`, `B p` remains strict true at all three source worlds. -/
theorem gate29_recoveryPreserving_belief_profile :
    evalModal Gate29RecoveryPreservingUpdated DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate29RecoveryPreservingUpdated DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate29RecoveryPreservingUpdated DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- Hence the safe branch preserves the full recursive Recovery contract. -/
theorem gate29_recoveryPreserving_update_recovered :
    ModalFormula.CompositionalRecovery
      Gate29RecoveryPreservingUpdated dynamicInstabilityBelP := by
  intro w
  constructor
  · intro u _
    cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rcases gate29_recoveryPreserving_belief_profile with ⟨ha, hb, hc⟩
    cases w
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate29RecoveryPreservingUpdated DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityP ha
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate29RecoveryPreservingUpdated DynamicInstabilityAgent.i
        DynamicInstabilityWorld.b dynamicInstabilityP hb
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate29RecoveryPreservingUpdated DynamicInstabilityAgent.i
        DynamicInstabilityWorld.c dynamicInstabilityP hc

/-- Concrete same-start split: the starting 4PEL model is recovered for `B p`;
both evidence choices are admissible; learning `p` preserves Recovery while
learning `e` destroys it. -/
theorem gate29_concrete_conditionalization_split :
    ModalFormula.CompositionalRecovery
        DynamicInstabilityModel dynamicInstabilityBelP ∧
    ConditionalizationAdmissible DynamicInstabilityModel
        gate29RecoveryPreservingEvidence ∧
    ModalFormula.CompositionalRecovery
        Gate29RecoveryPreservingUpdated dynamicInstabilityBelP ∧
    ConditionalizationAdmissible DynamicInstabilityModel
        dynamicInstabilityEvidence ∧
    ¬ ModalFormula.CompositionalRecovery
        DynamicInstabilityUpdated dynamicInstabilityBelP := by
  exact ⟨dynamic_instability_belP_recovered_before,
    gate29_recoveryPreservingEvidence_admissible,
    gate29_recoveryPreserving_update_recovered,
    dynamic_instability_evidence_admissible,
    dynamic_instability_belP_not_recovered_after⟩

end PEL4
