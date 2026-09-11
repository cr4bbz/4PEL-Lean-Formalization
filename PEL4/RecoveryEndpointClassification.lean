import PEL4.RecoveryEventualStability

namespace PEL4

/-!
# Gate 28: recovery endpoint classification

Gate 27 proves eventual constancy of the Boolean recovery status along every
infinite trajectory satisfying the Gate-26 descent contract.  Gate 28 isolates
what that theorem does and does not determine.

The positive result is an exact endpoint classification: every valid trajectory
is eventually always Recovery or eventually always Non-Recovery, and the two
endpoints are mutually exclusive.

The negative result is equally important: the descent contract itself does not
privilege Recovery.  Two minimal systems witness that both asymptotic endpoint
statuses are compatible with the same abstract theory.
-/

/-- A trajectory eventually has the specified recovery status forever. -/
def EventuallyRecoveryStatus
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) (target : Bool) : Prop :=
  ∃ N, ∀ n, N ≤ n -> sys.status (trajectory n) = target

/-- Eventual recovery stability over a Boolean status determines one of the two
possible endpoint statuses. -/
theorem eventuallyRecoveryStable_endpoint_classification
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hStable : EventuallyRecoveryStable sys trajectory) :
    EventuallyRecoveryStatus sys trajectory true ∨
      EventuallyRecoveryStatus sys trajectory false := by
  obtain ⟨N, hN⟩ := hStable
  cases hStatus : sys.status (trajectory N) with
  | false =>
      right
      refine ⟨N, ?_⟩
      intro n hn
      calc
        sys.status (trajectory n) = sys.status (trajectory N) := hN n hn
        _ = false := hStatus
  | true =>
      left
      refine ⟨N, ?_⟩
      intro n hn
      calc
        sys.status (trajectory n) = sys.status (trajectory N) := hN n hn
        _ = true := hStatus

/-- The two eventual Boolean endpoints cannot both occur on the same
trajectory. -/
theorem eventuallyRecoveryStatus_exclusive
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hTrue : EventuallyRecoveryStatus sys trajectory true)
    (hFalse : EventuallyRecoveryStatus sys trajectory false) : False := by
  obtain ⟨Nt, hT⟩ := hTrue
  obtain ⟨Nf, hF⟩ := hFalse
  have hTrueAt : sys.status (trajectory (Nt + Nf)) = true :=
    hT (Nt + Nf) (by omega)
  have hFalseAt : sys.status (trajectory (Nt + Nf)) = false :=
    hF (Nt + Nf) (by omega)
  have hImpossible : (true : Bool) = false := hTrueAt.symm.trans hFalseAt
  cases hImpossible

/-- Main classification theorem for valid infinite descent trajectories. -/
theorem recoveryTrajectory_endpoint_classification
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    EventuallyRecoveryStatus sys trajectory true ∨
      EventuallyRecoveryStatus sys trajectory false := by
  exact eventuallyRecoveryStable_endpoint_classification sys trajectory
    (recoveryTrajectory_eventuallyRecoveryStable sys trajectory hFollows)

/-- A valid trajectory has exactly one eventual recovery endpoint. -/
theorem recoveryTrajectory_exactly_one_endpoint
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    (EventuallyRecoveryStatus sys trajectory true ∧
      ¬ EventuallyRecoveryStatus sys trajectory false) ∨
    (EventuallyRecoveryStatus sys trajectory false ∧
      ¬ EventuallyRecoveryStatus sys trajectory true) := by
  rcases recoveryTrajectory_endpoint_classification sys trajectory hFollows with
    hTrue | hFalse
  · left
    refine ⟨hTrue, ?_⟩
    intro hFalse
    exact eventuallyRecoveryStatus_exclusive sys trajectory hTrue hFalse
  · right
    refine ⟨hFalse, ?_⟩
    intro hTrue
    exact eventuallyRecoveryStatus_exclusive sys trajectory hTrue hFalse

/-- Minimal descent system whose recovery status is permanently true. -/
def gate28RecoverySystem : RecoveryDescentSystem Unit where
  status := fun _ => true
  potential := fun _ => 0
  Step := fun _ _ => True
  step_budget := by
    intro s t hStep
    simp [recoveryChangeCost]

/-- Minimal descent system whose recovery status is permanently false. -/
def gate28NonRecoverySystem : RecoveryDescentSystem Unit where
  status := fun _ => false
  potential := fun _ => 0
  Step := fun _ _ => True
  step_budget := by
    intro s t hStep
    simp [recoveryChangeCost]

/-- Shared infinite trajectory for the two one-state witness systems. -/
def gate28UnitTrajectory : Nat -> Unit := fun _ => ()

theorem gate28_recoveryTrajectory_follows :
    recoveryTrajectoryFollows gate28RecoverySystem gate28UnitTrajectory := by
  intro n
  trivial

theorem gate28_nonRecoveryTrajectory_follows :
    recoveryTrajectoryFollows gate28NonRecoverySystem gate28UnitTrajectory := by
  intro n
  trivial

/-- Recovery itself is a possible asymptotic endpoint. -/
theorem gate28_recovery_endpoint_possible :
    EventuallyRecoveryStatus gate28RecoverySystem gate28UnitTrajectory true := by
  refine ⟨0, ?_⟩
  intro n hn
  rfl

/-- Non-Recovery is also a possible asymptotic endpoint under the same abstract
descent contract. -/
theorem gate28_nonRecovery_endpoint_possible :
    EventuallyRecoveryStatus gate28NonRecoverySystem gate28UnitTrajectory false := by
  refine ⟨0, ?_⟩
  intro n hn
  rfl

/-- Counterexample to the tempting over-reading of Gate 27: eventual stability
does not imply eventual Recovery. -/
theorem gate28_eventual_stability_does_not_force_recovery :
    EventuallyRecoveryStable gate28NonRecoverySystem gate28UnitTrajectory ∧
      ¬ EventuallyRecoveryStatus gate28NonRecoverySystem gate28UnitTrajectory true := by
  constructor
  · exact recoveryTrajectory_eventuallyRecoveryStable
      gate28NonRecoverySystem gate28UnitTrajectory
      gate28_nonRecoveryTrajectory_follows
  · intro hTrue
    exact eventuallyRecoveryStatus_exclusive
      gate28NonRecoverySystem gate28UnitTrajectory
      hTrue gate28_nonRecovery_endpoint_possible

end PEL4
