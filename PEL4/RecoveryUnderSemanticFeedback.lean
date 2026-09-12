import PEL4.RecoveryEpistemicAttractor
import PEL4.RegenerativeRecoveryBudget
import PEL4.StrongHysteresisBoundary

namespace PEL4

/-!
# Gate 41: Recovery under semantic feedback

Gate 33 showed that endogenous evidence can produce Recovery hysteresis. Gate 34
showed that epistemic resource can be regenerated, so early Recovery flips need
not be paid for by the initial potential alone. Gate 40 isolated semantic
extension feedback as a necessary ingredient of the verified two-step
hysteresis phenomenon.

Gate 41 asks whether such an early history permanently blocks convergence. The
answer is no under an explicit tail condition. A trajectory may have an
arbitrary regenerative prefix. Once it reaches a cutoff `K` after which

* no further resource is regenerated,
* Recovery is absorbing along the actual future trajectory, and
* every Non-Recovery step strictly consumes the remaining finite potential,

then permanent Recovery is reached no later than

`K + potential (trajectory K)`.

The theorem is deliberately trajectory-local after the cutoff. We do not assume
that every transition admitted by the ambient update relation is attractive,
only that the realized tail is.
-/

/-- Infinite trajectory version of Gate 34's regenerative step relation. -/
def recoveryRegenerativeTrajectoryFollows
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State) : Prop :=
  ∀ n, sys.Step (trajectory n) (trajectory (n + 1))

/-- No new finite Recovery resource is created on the realized tail starting at
`K`. The prefix before `K` remains unconstrained and may regenerate resource. -/
def RegenerationCeasesAfter
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State) (K : Nat) : Prop :=
  ∀ n,
    sys.regeneration (trajectory (K + n))
      (trajectory (K + n + 1)) = 0

/-- Once Recovery occurs on the realized tail, the next realized state remains
in Recovery. -/
def RecoveryAbsorbingAfter
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State) (K : Nat) : Prop :=
  ∀ n,
    sys.status (trajectory (K + n)) = true ->
      sys.status (trajectory (K + n + 1)) = true

/-- Every realized update that starts in Non-Recovery after the cutoff strictly
consumes the remaining finite potential. -/
def NonRecoveryConsumesPotentialAfter
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State) (K : Nat) : Prop :=
  ∀ n,
    sys.status (trajectory (K + n)) = false ->
      sys.potential (trajectory (K + n + 1)) <
        sys.potential (trajectory (K + n))

/-- Compile the realized zero-regeneration tail into an ordinary Gate-26
descent system whose states are time indices. This avoids imposing attractive
properties on unrealized branches of the ambient transition relation. -/
def regenerativeTailDescentSystem
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryRegenerativeTrajectoryFollows sys trajectory)
    (K : Nat)
    (hNoRegeneration : RegenerationCeasesAfter sys trajectory K) :
    RecoveryDescentSystem Nat where
  status := fun n => sys.status (trajectory (K + n))
  potential := fun n => sys.potential (trajectory (K + n))
  Step := fun n m => m = n + 1
  step_budget := by
    intro n m hStep
    subst m
    have hBudget := sys.step_budget (hFollows (K + n))
    have hZero := hNoRegeneration n
    rw [hZero] at hBudget
    simpa [Nat.add_assoc] using hBudget

/-- The identity trajectory follows the time-indexed tail system. -/
theorem regenerativeTailDescentSystem_id_follows
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryRegenerativeTrajectoryFollows sys trajectory)
    (K : Nat)
    (hNoRegeneration : RegenerationCeasesAfter sys trajectory K) :
    recoveryTrajectoryFollows
      (regenerativeTailDescentSystem sys trajectory hFollows K hNoRegeneration)
      (fun n => n) := by
  intro n
  rfl

/-- Tail-local absorption is exactly global absorption in the compiled
index system. -/
theorem regenerativeTailDescentSystem_absorbing
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryRegenerativeTrajectoryFollows sys trajectory)
    (K : Nat)
    (hNoRegeneration : RegenerationCeasesAfter sys trajectory K)
    (hAbsorbing : RecoveryAbsorbingAfter sys trajectory K) :
    RecoveryAbsorbing
      (regenerativeTailDescentSystem sys trajectory hFollows K hNoRegeneration) := by
  intro n m hStep hTrue
  change m = n + 1 at hStep
  subst m
  change sys.status (trajectory (K + (n + 1))) = true
  have hNext := hAbsorbing n (by
    simpa [regenerativeTailDescentSystem] using hTrue)
  simpa [Nat.add_assoc] using hNext

/-- Tail-local strict consumption is exactly the Gate-32 consumption condition
in the compiled index system. -/
theorem regenerativeTailDescentSystem_consumes
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryRegenerativeTrajectoryFollows sys trajectory)
    (K : Nat)
    (hNoRegeneration : RegenerationCeasesAfter sys trajectory K)
    (hConsumes : NonRecoveryConsumesPotentialAfter sys trajectory K) :
    NonRecoveryConsumesPotential
      (regenerativeTailDescentSystem sys trajectory hFollows K hNoRegeneration) := by
  intro n m hStep hFalse
  change m = n + 1 at hStep
  subst m
  change
    sys.potential (trajectory (K + (n + 1))) <
      sys.potential (trajectory (K + n))
  have hDrop := hConsumes n (by
    simpa [regenerativeTailDescentSystem] using hFalse)
  simpa [Nat.add_assoc] using hDrop

/-- Main Gate-41 theorem. An arbitrary regenerative prefix is harmless once the
realized future enters a zero-regeneration Recovery-attractor regime. Permanent
Recovery is reached within the potential remaining at the cutoff. -/
theorem recoveryRegenerative_eventuallyRecovery_after_cutoff
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryRegenerativeTrajectoryFollows sys trajectory)
    (K : Nat)
    (hNoRegeneration : RegenerationCeasesAfter sys trajectory K)
    (hAbsorbing : RecoveryAbsorbingAfter sys trajectory K)
    (hConsumes : NonRecoveryConsumesPotentialAfter sys trajectory K) :
    ∃ N,
      K ≤ N ∧
      N ≤ K + sys.potential (trajectory K) ∧
      ∀ n, N ≤ n -> sys.status (trajectory n) = true := by
  let tailSys :=
    regenerativeTailDescentSystem sys trajectory hFollows K hNoRegeneration
  have hTailFollows : recoveryTrajectoryFollows tailSys (fun n => n) := by
    exact regenerativeTailDescentSystem_id_follows
      sys trajectory hFollows K hNoRegeneration
  have hTailAbsorbing : RecoveryAbsorbing tailSys := by
    exact regenerativeTailDescentSystem_absorbing
      sys trajectory hFollows K hNoRegeneration hAbsorbing
  have hTailConsumes : NonRecoveryConsumesPotential tailSys := by
    exact regenerativeTailDescentSystem_consumes
      sys trajectory hFollows K hNoRegeneration hConsumes
  obtain ⟨j, hjBound, hRecovery⟩ :=
    recoveryTrajectory_eventuallyRecovery_of_attractorContract
      tailSys (fun n => n) hTailFollows hTailAbsorbing hTailConsumes
  have hjBound' : j ≤ sys.potential (trajectory K) := by
    simpa [tailSys, regenerativeTailDescentSystem] using hjBound
  refine ⟨K + j, by omega, by omega, ?_⟩
  intro n hn
  let r := n - K
  have hKr : K + r = n := by
    dsimp [r]
    omega
  have hjr : j ≤ r := by
    dsimp [r]
    omega
  have hTrue := hRecovery r hjr
  have hTrue' : sys.status (trajectory (K + r)) = true := by
    simpa [tailSys, regenerativeTailDescentSystem] using hTrue
  rwa [hKr] at hTrue'

/-! ## Sharp turbulent-prefix witness -/

inductive Gate41State where
  | start
  | fractured
  | cutoff
  | recovered
  deriving DecidableEq, Repr

inductive Gate41Step : Gate41State -> Gate41State -> Prop where
  | fracture : Gate41Step .start .fractured
  | settle : Gate41Step .fractured .cutoff
  | recover : Gate41Step .cutoff .recovered
  | stayRecovered : Gate41Step .recovered .recovered

/-- The first edge creates one resource unit and funds an early Recovery loss.
After the cutoff no regeneration occurs and the remaining unit funds the final
return to Recovery. -/
def gate41RegenerativeSystem : RecoveryRegenerativeSystem Gate41State where
  status
    | .start => true
    | .fractured => false
    | .cutoff => false
    | .recovered => true
  potential
    | .start => 1
    | .fractured => 1
    | .cutoff => 1
    | .recovered => 0
  regeneration
    | .start, .fractured => 1
    | _, _ => 0
  Step := Gate41Step
  step_budget := by
    intro s t hStep
    cases hStep <;> decide

/-- A regenerative turbulent prefix followed by a permanent Recovery tail. -/
def gate41Trajectory : Nat -> Gate41State
  | 0 => .start
  | 1 => .fractured
  | 2 => .cutoff
  | _ => .recovered

theorem gate41_trajectory_follows :
    recoveryRegenerativeTrajectoryFollows
      gate41RegenerativeSystem gate41Trajectory := by
  intro n
  cases n with
  | zero => exact Gate41Step.fracture
  | succ n =>
      cases n with
      | zero => exact Gate41Step.settle
      | succ n =>
          cases n with
          | zero => exact Gate41Step.recover
          | succ n => exact Gate41Step.stayRecovered

theorem gate41_regeneration_ceases_after_two :
    RegenerationCeasesAfter gate41RegenerativeSystem gate41Trajectory 2 := by
  intro n
  cases n <;> rfl

theorem gate41_recovery_absorbing_after_two :
    RecoveryAbsorbingAfter gate41RegenerativeSystem gate41Trajectory 2 := by
  intro n hTrue
  cases n with
  | zero =>
      simp [gate41RegenerativeSystem, gate41Trajectory] at hTrue
  | succ n => rfl

theorem gate41_nonRecovery_consumes_after_two :
    NonRecoveryConsumesPotentialAfter
      gate41RegenerativeSystem gate41Trajectory 2 := by
  intro n hFalse
  cases n with
  | zero => decide
  | succ n =>
      simp [gate41RegenerativeSystem, gate41Trajectory] at hFalse

/-- Gate 41 permits a genuinely regenerative, status-changing prefix and still
forces permanent Recovery once the tail contract begins. -/
theorem gate41_turbulence_then_permanent_recovery :
    ∃ N,
      2 ≤ N ∧
      N ≤ 2 + gate41RegenerativeSystem.potential (gate41Trajectory 2) ∧
      ∀ n, N ≤ n ->
        gate41RegenerativeSystem.status (gate41Trajectory n) = true := by
  exact recoveryRegenerative_eventuallyRecovery_after_cutoff
    gate41RegenerativeSystem gate41Trajectory gate41_trajectory_follows 2
    gate41_regeneration_ceases_after_two
    gate41_recovery_absorbing_after_two
    gate41_nonRecovery_consumes_after_two

/-- The generic Gate-41 deadline is attained exactly by the witness: the cutoff
is at `2`, one unit remains, and Recovery first becomes permanent at `3`. -/
theorem gate41_cutoff_bound_is_sharp :
    gate41RegenerativeSystem.status (gate41Trajectory 2) = false ∧
    (∀ n, 3 ≤ n ->
      gate41RegenerativeSystem.status (gate41Trajectory n) = true) ∧
    3 = 2 + gate41RegenerativeSystem.potential (gate41Trajectory 2) := by
  constructor
  · decide
  constructor
  · intro n hn
    cases n with
    | zero => omega
    | succ n =>
        cases n with
        | zero => omega
        | succ n =>
            cases n with
            | zero => omega
            | succ n => rfl
  · decide

/-!
## Gate-41 conclusion

The dynamics now separate into two temporal regimes:

```text
prefix < K:
  semantic feedback / regeneration / Recovery flips may occur

suffix >= K:
  no regeneration
  + Recovery absorption along the realized path
  + strict potential consumption in Non-Recovery
  => permanent Recovery by K + remaining potential.
```

So hysteresis is not by itself an obstruction to eventual Recovery. What matters
is whether semantic feedback remains indefinitely resource-regenerating or the
future eventually enters a genuinely dissipative Recovery-attractor regime.

This is a sufficient-condition theorem. Gate 41 does not claim that semantic
feedback must cease in real epistemic learning, nor that Recovery corresponds
to correspondence truth. `Recovery` retains its formal meaning as the verified
classical/compositional phase of the current 4PEL framework.
-/

end PEL4
