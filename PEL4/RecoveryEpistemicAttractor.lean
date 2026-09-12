import PEL4.RecoveryEndpointClassification
import PEL4.RecoveryStabilizationBounds

namespace PEL4

/-!
# Gate 32: Recovery as epistemic attractor

Gates 27--31 establish that Recovery status has finite variation, eventually
stabilizes, admits two possible endpoints, may depend on the update path, can
be confluent under suitable update equivalence, and can satisfy quantitative
stabilization deadlines under bounded progress.

None of those results privilege Recovery over Non-Recovery. Gate 32 isolates
the additional directional condition needed to make Recovery an epistemic
attractor.

The gate has two layers.

* `NonRecoveryTransientAlong` is the exact trajectory-level condition excluding
  a permanently trapped Non-Recovery phase.
* `RecoveryAbsorbing` plus `NonRecoveryConsumesPotential` is a stronger local
  update contract: once Recovery is reached it persists, while every update
  taken in Non-Recovery strictly consumes the finite natural-valued potential.

The second layer turns the Gate-26 potential into a genuine distance-to-
Recovery resource and yields a quantitative attraction bound.
-/

/-- Non-Recovery is transient along a trajectory: every Non-Recovery time has
some strictly later Recovery time. -/
def NonRecoveryTransientAlong
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) : Prop :=
  ∀ n, sys.status (trajectory n) = false ->
    ∃ m, n < m ∧ sys.status (trajectory m) = true

/-- Eventual permanent Recovery implies that every earlier Non-Recovery point
is transient. -/
theorem eventuallyRecoveryStatus_implies_nonRecoveryTransient
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hEventually : EventuallyRecoveryStatus sys trajectory true) :
    NonRecoveryTransientAlong sys trajectory := by
  intro n hFalse
  obtain ⟨N, hRecovery⟩ := hEventually
  let m := N + n + 1
  refine ⟨m, ?_, ?_⟩
  · dsimp [m]
    omega
  · exact hRecovery m (by
      dsimp [m]
      omega)

/-- On a valid finite-descent trajectory, transience of every Non-Recovery
point rules out the Non-Recovery endpoint and therefore forces eventual
permanent Recovery. -/
theorem recoveryTrajectory_eventuallyRecovery_of_nonRecoveryTransient
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (hTransient : NonRecoveryTransientAlong sys trajectory) :
    EventuallyRecoveryStatus sys trajectory true := by
  rcases recoveryTrajectory_endpoint_classification sys trajectory hFollows with
    hRecovery | hNonRecovery
  · exact hRecovery
  · obtain ⟨N, hFalseFrom⟩ := hNonRecovery
    have hFalseN : sys.status (trajectory N) = false :=
      hFalseFrom N (by omega)
    obtain ⟨m, hNm, hTrueM⟩ := hTransient N hFalseN
    have hFalseM : sys.status (trajectory m) = false :=
      hFalseFrom m (by omega)
    have hImpossible : (true : Bool) = false := hTrueM.symm.trans hFalseM
    cases hImpossible

/-- Exact Gate-32 endpoint criterion for valid trajectories: eventual permanent
Recovery is equivalent to the absence of a permanently trapped Non-Recovery
phase. -/
theorem recoveryTrajectory_eventuallyRecovery_iff_nonRecoveryTransient
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    EventuallyRecoveryStatus sys trajectory true ↔
      NonRecoveryTransientAlong sys trajectory := by
  constructor
  · exact eventuallyRecoveryStatus_implies_nonRecoveryTransient sys trajectory
  · exact recoveryTrajectory_eventuallyRecovery_of_nonRecoveryTransient
      sys trajectory hFollows

/-- Gate-31 bounded progress plus Gate-32 Non-Recovery transience yields not
merely a stabilization deadline, but a Recovery deadline with the same sharp
resource bound. -/
theorem recoveryTrajectory_recoveredBy_of_boundedProgress
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (B : Nat)
    (hProgress : BoundedRecoveryProgress sys trajectory B)
    (hTransient : NonRecoveryTransientAlong sys trajectory) :
    ∃ N,
      N ≤ B * sys.potential (trajectory 0) ∧
      ∀ n, N ≤ n -> sys.status (trajectory n) = true := by
  obtain ⟨N, hNBound, hStable⟩ :=
    recoveryTrajectory_stabilizesBy sys trajectory hFollows B hProgress
  have hAtN : sys.status (trajectory N) = true := by
    cases hStatus : sys.status (trajectory N) with
    | false =>
        obtain ⟨m, hNm, hTrueM⟩ := hTransient N hStatus
        have hSame :
            sys.status (trajectory m) = sys.status (trajectory N) :=
          hStable m (by omega)
        have hFalseM : sys.status (trajectory m) = false :=
          hSame.trans hStatus
        have hImpossible : (true : Bool) = false := hTrueM.symm.trans hFalseM
        cases hImpossible
    | true => exact hStatus
  refine ⟨N, hNBound, ?_⟩
  intro n hn
  calc
    sys.status (trajectory n) = sys.status (trajectory N) := hStable n hn
    _ = true := hAtN

/-! ## Local structural attractor contract -/

/-- Recovery is absorbing at the update-relation level. -/
def RecoveryAbsorbing
    {State : Type} (sys : RecoveryDescentSystem State) : Prop :=
  ∀ {s t : State}, sys.Step s t ->
    sys.status s = true -> sys.status t = true

/-- Every update performed while still in Non-Recovery strictly decreases the
finite potential, even if the Boolean status itself does not yet flip. -/
def NonRecoveryConsumesPotential
    {State : Type} (sys : RecoveryDescentSystem State) : Prop :=
  ∀ {s t : State}, sys.Step s t ->
    sys.status s = false -> sys.potential t < sys.potential s

/-- Once a trajectory starts in Recovery inside an absorbing system, it remains
in Recovery forever. -/
theorem recoveryAbsorbing_from_zero
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (hAbsorbing : RecoveryAbsorbing sys)
    (hStart : sys.status (trajectory 0) = true) :
    ∀ n, sys.status (trajectory n) = true := by
  intro n
  induction n with
  | zero => exact hStart
  | succ n ih =>
      exact hAbsorbing (hFollows n) ih

/-- Quantitative attraction lemma. If the initial potential is at most `p`,
then an absorbing Recovery phase together with strict potential consumption in
Non-Recovery guarantees that Recovery has been reached by time `p`. -/
theorem recoveryAttractor_status_true_by_of_initialPotential_le
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (hAbsorbing : RecoveryAbsorbing sys)
    (hConsumes : NonRecoveryConsumesPotential sys)
    (p : Nat)
    (hBound : sys.potential (trajectory 0) ≤ p) :
    sys.status (trajectory p) = true := by
  induction p generalizing trajectory with
  | zero =>
      have hPotentialZero : sys.potential (trajectory 0) = 0 := by omega
      cases hStatus : sys.status (trajectory 0) with
      | true => exact hStatus
      | false =>
          have hStrict := hConsumes (hFollows 0) hStatus
          omega
  | succ p ih =>
      cases hStatus : sys.status (trajectory 0) with
      | true =>
          have hAll := recoveryAbsorbing_from_zero
            sys trajectory hFollows hAbsorbing hStatus
          exact hAll (p + 1)
      | false =>
          let tail : Nat -> State := fun j => trajectory (1 + j)
          have hTailFollows : recoveryTrajectoryFollows sys tail := by
            exact recoveryTrajectoryFollows_tail sys trajectory 1 hFollows
          have hStrict :
              sys.potential (trajectory 1) <
                sys.potential (trajectory 0) := by
            simpa using hConsumes (hFollows 0) hStatus
          have hTailBound : sys.potential (tail 0) ≤ p := by
            dsimp [tail]
            omega
          have hTailTrue := ih tail hTailFollows hTailBound
          dsimp [tail] at hTailTrue
          simpa [Nat.add_comm] using hTailTrue

/-- Main structural Gate-32 theorem: under the local attractor contract,
Recovery is reached within the initial potential and is permanent thereafter. -/
theorem recoveryTrajectory_eventuallyRecovery_of_attractorContract
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (hAbsorbing : RecoveryAbsorbing sys)
    (hConsumes : NonRecoveryConsumesPotential sys) :
    ∃ N,
      N ≤ sys.potential (trajectory 0) ∧
      ∀ n, N ≤ n -> sys.status (trajectory n) = true := by
  let p := sys.potential (trajectory 0)
  have hAtP : sys.status (trajectory p) = true := by
    exact recoveryAttractor_status_true_by_of_initialPotential_le
      sys trajectory hFollows hAbsorbing hConsumes p (by omega)
  let tail : Nat -> State := fun j => trajectory (p + j)
  have hTailFollows : recoveryTrajectoryFollows sys tail := by
    exact recoveryTrajectoryFollows_tail sys trajectory p hFollows
  have hTailStart : sys.status (tail 0) = true := by
    simpa [tail] using hAtP
  have hAllTail := recoveryAbsorbing_from_zero
    sys tail hTailFollows hAbsorbing hTailStart
  refine ⟨p, by simp [p], ?_⟩
  intro n hn
  let j := n - p
  have hpj : p + j = n := by
    dsimp [j]
    omega
  have hTrue := hAllTail j
  dsimp [tail] at hTrue
  rw [hpj] at hTrue
  exact hTrue

/-- The structural attractor contract implies the trajectory-level exact
criterion and hence eventual permanent Recovery. -/
theorem recoveryAttractorContract_implies_nonRecoveryTransient
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (hAbsorbing : RecoveryAbsorbing sys)
    (hConsumes : NonRecoveryConsumesPotential sys) :
    NonRecoveryTransientAlong sys trajectory := by
  apply eventuallyRecoveryStatus_implies_nonRecoveryTransient sys trajectory
  obtain ⟨N, hNBound, hRecovery⟩ :=
    recoveryTrajectory_eventuallyRecovery_of_attractorContract
      sys trajectory hFollows hAbsorbing hConsumes
  exact ⟨N, hRecovery⟩

/-! ## Minimal attractor witness -/

inductive Gate32State where
  | nonRecovery
  | recovery
  deriving DecidableEq, Repr

def gate32Status : Gate32State -> Bool
  | .nonRecovery => false
  | .recovery => true

def gate32Potential : Gate32State -> Nat
  | .nonRecovery => 1
  | .recovery => 0

inductive Gate32Step : Gate32State -> Gate32State -> Prop where
  | recover : Gate32Step .nonRecovery .recovery
  | stayRecovered : Gate32Step .recovery .recovery

def gate32AttractorSystem : RecoveryDescentSystem Gate32State where
  status := gate32Status
  potential := gate32Potential
  Step := Gate32Step
  step_budget := by
    intro s t hStep
    cases hStep <;> decide

def gate32AttractorTrajectory : Nat -> Gate32State
  | 0 => .nonRecovery
  | _ + 1 => .recovery

theorem gate32_attractor_trajectory_follows :
    recoveryTrajectoryFollows gate32AttractorSystem
      gate32AttractorTrajectory := by
  intro n
  cases n with
  | zero => exact Gate32Step.recover
  | succ n => exact Gate32Step.stayRecovered

theorem gate32_attractor_absorbing :
    RecoveryAbsorbing gate32AttractorSystem := by
  intro s t hStep hTrue
  cases hStep
  · decide at hTrue
  · rfl

theorem gate32_attractor_consumes_nonRecovery :
    NonRecoveryConsumesPotential gate32AttractorSystem := by
  intro s t hStep hFalse
  cases hStep
  · decide
  · decide at hFalse

theorem gate32_attractor_recovery_is_permanent :
    EventuallyRecoveryStatus gate32AttractorSystem
      gate32AttractorTrajectory true := by
  obtain ⟨N, hNBound, hRecovery⟩ :=
    recoveryTrajectory_eventuallyRecovery_of_attractorContract
      gate32AttractorSystem gate32AttractorTrajectory
      gate32_attractor_trajectory_follows
      gate32_attractor_absorbing
      gate32_attractor_consumes_nonRecovery
  exact ⟨N, hRecovery⟩

/-- The Gate-28 permanently Non-Recovery system is excluded by the new
attractor contract: while Non-Recovery it can stutter forever at zero
potential. -/
theorem gate32_gate28_nonRecovery_not_potential_consuming :
    ¬ NonRecoveryConsumesPotential gate28NonRecoverySystem := by
  intro hConsumes
  have hImpossible := hConsumes (s := ()) (t := ()) trivial rfl
  simpa [gate28NonRecoverySystem] using hImpossible

end PEL4
