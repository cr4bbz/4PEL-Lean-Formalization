import PEL4.RecoveryEventualStability

namespace PEL4

/-!
# Gate 31: Progress and stabilization bounds

Gate 27 proves eventual recovery-status stability from a finite descent
potential, but gives no numerical deadline: arbitrarily long status-preserving
stuttering may separate the finitely many genuine changes.

Gate 31 adds a bounded-liveness hypothesis. If the current recovery phase will
ever be left again, then some adjacent recovery-status change must occur within
the next `B` update edges. Combined with the Gate-26 fact that every such
change consumes at least one unit of natural-valued potential, this turns the
qualitative eventual-stability theorem into an explicit deadline.
-/

/-- Recovery status is already permanently constant from time `N` onward. -/
def RecoveryStabilizesBy
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) (N : Nat) : Prop :=
  ∀ n, N ≤ n ->
    sys.status (trajectory n) = sys.status (trajectory N)

/-- Bounded recovery progress: whenever the status at time `n` will differ at
some later time, an adjacent status-changing edge occurs within the next `B`
edges. For `B = 0`, this forces immediate permanent status stability. -/
def BoundedRecoveryProgress
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) (B : Nat) : Prop :=
  ∀ n,
    (∃ m, n < m ∧
      sys.status (trajectory m) ≠ sys.status (trajectory n)) ->
    ∃ k, k < B ∧
      sys.status (trajectory (n + k)) ≠
        sys.status (trajectory (n + k + 1))

/-- A bounded-progress hypothesis survives passage to any suffix trajectory. -/
theorem boundedRecoveryProgress_tail
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) (B offset : Nat)
    (hProgress : BoundedRecoveryProgress sys trajectory B) :
    BoundedRecoveryProgress sys (fun j => trajectory (offset + j)) B := by
  intro n hFuture
  obtain ⟨m, hnm, hNe⟩ := hFuture
  have hGlobalFuture :
      ∃ m', offset + n < m' ∧
        sys.status (trajectory m') ≠
          sys.status (trajectory (offset + n)) := by
    refine ⟨offset + m, by omega, ?_⟩
    simpa [Nat.add_assoc] using hNe
  obtain ⟨k, hkB, hChange⟩ := hProgress (offset + n) hGlobalFuture
  refine ⟨k, hkB, ?_⟩
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hChange

/-- A trajectory suffix still follows the same update relation. -/
theorem recoveryTrajectoryFollows_tail
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) (offset : Nat)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    recoveryTrajectoryFollows sys (fun j => trajectory (offset + j)) := by
  intro j
  change sys.Step (trajectory (offset + j)) (trajectory (offset + (j + 1)))
  simpa [Nat.add_assoc] using hFollows (offset + j)

/-- Quantitative bounded-potential induction. If the initial potential is at
most `p`, then bounded progress with horizon `B` yields a stabilization time no
later than `B * p`. -/
theorem recoveryTrajectory_stabilizesBy_of_initialPotential_le
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (B p : Nat)
    (hProgress : BoundedRecoveryProgress sys trajectory B)
    (hBound : sys.potential (trajectory 0) ≤ p) :
    ∃ N, N ≤ B * p ∧ RecoveryStabilizesBy sys trajectory N := by
  induction p generalizing trajectory with
  | zero =>
      have hZero : sys.potential (trajectory 0) = 0 := by omega
      refine ⟨0, by simp, ?_⟩
      intro n hn
      simpa using
        recoveryTrajectory_status_eq_initial_of_zero_potential
          sys trajectory hFollows hZero n
  | succ p ih =>
      by_cases hAll :
          ∀ n, sys.status (trajectory n) = sys.status (trajectory 0)
      · refine ⟨0, by simp, ?_⟩
        intro n hn
        simpa using hAll n
      · have hExists :
            ∃ m, 0 < m ∧
              sys.status (trajectory m) ≠ sys.status (trajectory 0) := by
          have hRaw :
              ∃ m, sys.status (trajectory m) ≠
                sys.status (trajectory 0) :=
            Classical.not_forall.mp hAll
          obtain ⟨m, hNe⟩ := hRaw
          have hm : 0 < m := by
            cases m with
            | zero => exact False.elim (hNe rfl)
            | succ m => omega
          exact ⟨m, hm, hNe⟩
        obtain ⟨k, hkB, hChange⟩ := hProgress 0 hExists
        let offset := k + 1
        let tail : Nat -> State := fun j => trajectory (offset + j)
        have hTailFollows : recoveryTrajectoryFollows sys tail := by
          exact recoveryTrajectoryFollows_tail sys trajectory offset hFollows
        have hTailProgress : BoundedRecoveryProgress sys tail B := by
          exact boundedRecoveryProgress_tail sys trajectory B offset hProgress
        have hKLe :
            sys.potential (trajectory k) ≤
              sys.potential (trajectory 0) :=
          recoveryTrajectory_potential_le_initial sys trajectory hFollows k
        have hK1Lt :
            sys.potential (trajectory (k + 1)) <
              sys.potential (trajectory k) :=
          sys.potential_lt_of_status_change (hFollows k) hChange
        have hTailBound : sys.potential (tail 0) ≤ p := by
          dsimp [tail, offset]
          omega
        obtain ⟨N, hNBound, hNStable⟩ :=
          ih tail hTailFollows hTailProgress hTailBound
        refine ⟨offset + N, ?_, ?_⟩
        · dsimp [offset]
          have hk1 : k + 1 ≤ B := by omega
          omega
        · intro n hn
          let j := n - offset
          have hOffsetLe : offset ≤ n := by omega
          have hjEq : offset + j = n := by
            dsimp [j]
            omega
          have hNj : N ≤ j := by
            dsimp [j]
            omega
          have hStable := hNStable j hNj
          dsimp [tail] at hStable
          rw [hjEq] at hStable
          exact hStable

/-- Main Gate-31 theorem: bounded progress converts the initial finite recovery
resource directly into a concrete stabilization deadline. -/
theorem recoveryTrajectory_stabilizesBy
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (B : Nat)
    (hProgress : BoundedRecoveryProgress sys trajectory B) :
    ∃ N,
      N ≤ B * sys.potential (trajectory 0) ∧
      RecoveryStabilizesBy sys trajectory N := by
  exact recoveryTrajectory_stabilizesBy_of_initialPotential_le
    sys trajectory hFollows B (sys.potential (trajectory 0))
      hProgress (by omega)

/-- The quantitative theorem subsumes qualitative eventual stability. -/
theorem eventuallyRecoveryStable_of_boundedProgress
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (B : Nat)
    (hProgress : BoundedRecoveryProgress sys trajectory B) :
    EventuallyRecoveryStable sys trajectory := by
  obtain ⟨N, hNBound, hStable⟩ :=
    recoveryTrajectory_stabilizesBy sys trajectory hFollows B hProgress
  exact ⟨N, hStable⟩

/-! ## Sharpness witness

With `B = 3` and initial potential `2`, the trajectory below stutters twice,
flips at edge 2, stutters twice again, flips at edge 5, and is then frozen.
Its first valid stabilization index is exactly `6 = 3 * 2`.
-/

def gate31SharpTrajectory (n : Nat) : RecoveryBudgetSnapshot :=
  if n < 3 then
    { status := true, potential := 2 }
  else if n < 6 then
    { status := false, potential := 1 }
  else
    { status := true, potential := 0 }

theorem gate31_sharp_trajectory_follows :
    recoveryTrajectoryFollows recoveryBudgetSnapshotSystem
      gate31SharpTrajectory := by
  intro n
  simp only [recoveryBudgetSnapshotSystem, gate31SharpTrajectory,
    recoveryChangeCost]
  by_cases h2 : n < 2
  · have hn3 : n < 3 := by omega
    have hn13 : n + 1 < 3 := by omega
    simp [hn3, hn13]
  · by_cases hn2 : n = 2
    · subst n
      decide
    · have hn3 : 3 ≤ n := by omega
      by_cases h5 : n < 5
      · have hn6 : n < 6 := by omega
        have hn16 : n + 1 < 6 := by omega
        simp [show ¬ n < 3 by omega, show ¬ n + 1 < 3 by omega,
          hn6, hn16]
      · by_cases hn5 : n = 5
        · subst n
          decide
        · have hn6 : 6 ≤ n := by omega
          simp [show ¬ n < 3 by omega, show ¬ n + 1 < 3 by omega,
            show ¬ n < 6 by omega, show ¬ n + 1 < 6 by omega]

theorem gate31_sharp_bounded_progress :
    BoundedRecoveryProgress recoveryBudgetSnapshotSystem
      gate31SharpTrajectory 3 := by
  intro n hFuture
  by_cases hn3 : n < 3
  · by_cases hn2 : n < 2
    · refine ⟨2 - n, ?_, ?_⟩
      · omega
      · have hnk : n + (2 - n) = 2 := by omega
        rw [hnk]
        decide
    · have hn2eq : n = 2 := by omega
      subst n
      exact ⟨0, by omega, by decide⟩
  · by_cases hn6 : n < 6
    · by_cases hn5 : n < 5
      · refine ⟨5 - n, ?_, ?_⟩
        · omega
        · have hnk : n + (5 - n) = 5 := by omega
          rw [hnk]
          decide
      · have hn5eq : n = 5 := by omega
        subst n
        exact ⟨0, by omega, by decide⟩
    · exfalso
      obtain ⟨m, hnm, hNe⟩ := hFuture
      have hnStatus :
          recoveryBudgetSnapshotSystem.status (gate31SharpTrajectory n) = true := by
        simp [recoveryBudgetSnapshotSystem, gate31SharpTrajectory,
          show ¬ n < 3 by omega, show ¬ n < 6 by omega]
      have hmStatus :
          recoveryBudgetSnapshotSystem.status (gate31SharpTrajectory m) = true := by
        simp [recoveryBudgetSnapshotSystem, gate31SharpTrajectory,
          show ¬ m < 3 by omega, show ¬ m < 6 by omega]
      exact hNe (hmStatus.trans hnStatus.symm)

theorem gate31_sharp_stabilizes_by_six :
    RecoveryStabilizesBy recoveryBudgetSnapshotSystem
      gate31SharpTrajectory 6 := by
  intro n hn
  simp [recoveryBudgetSnapshotSystem, gate31SharpTrajectory,
    show ¬ 6 < 3 by omega, show ¬ 6 < 6 by omega,
    show ¬ n < 3 by omega, show ¬ n < 6 by omega]

theorem gate31_sharp_not_stabilizes_by_five :
    ¬ RecoveryStabilizesBy recoveryBudgetSnapshotSystem
      gate31SharpTrajectory 5 := by
  intro hStable
  have h := hStable 6 (by omega)
  have h5 :
      recoveryBudgetSnapshotSystem.status (gate31SharpTrajectory 5) = false := by
    decide
  have h6 :
      recoveryBudgetSnapshotSystem.status (gate31SharpTrajectory 6) = true := by
    decide
  rw [h6, h5] at h
  decide at h

theorem gate31_sharp_hits_bound :
    6 = 3 * recoveryBudgetSnapshotSystem.potential
      (gate31SharpTrajectory 0) := by
  decide

/-- Gate-31 sharpness package: the generic deadline can be attained exactly. -/
theorem gate31_stabilization_bound_is_sharp :
    recoveryTrajectoryFollows recoveryBudgetSnapshotSystem gate31SharpTrajectory ∧
    BoundedRecoveryProgress recoveryBudgetSnapshotSystem gate31SharpTrajectory 3 ∧
    RecoveryStabilizesBy recoveryBudgetSnapshotSystem gate31SharpTrajectory 6 ∧
    ¬ RecoveryStabilizesBy recoveryBudgetSnapshotSystem gate31SharpTrajectory 5 ∧
    6 = 3 * recoveryBudgetSnapshotSystem.potential
      (gate31SharpTrajectory 0) := by
  exact ⟨gate31_sharp_trajectory_follows,
    gate31_sharp_bounded_progress,
    gate31_sharp_stabilizes_by_six,
    gate31_sharp_not_stabilizes_by_five,
    gate31_sharp_hits_bound⟩

end PEL4
