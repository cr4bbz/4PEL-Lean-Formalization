import PEL4.FiniteEpistemicDescent

namespace PEL4

/-!
# Gate 27: eventual recovery stability

Gate 26 bounded the number of recovery-status changes on every finite path by a
natural-valued descent potential.  Gate 27 asks what this means for an infinite
update trajectory.

The answer is stronger than a finite-prefix bound and weaker than convergence
of the underlying epistemic states: every infinite trajectory satisfying the
Gate-26 descent contract is eventually constant in recovery status.  The states
may continue to change forever, and status-preserving updates may occur
arbitrarily late, but recovery/non-recovery cannot oscillate infinitely often.
-/

/-- An infinite trajectory follows the abstract update relation at every
successor step. -/
def recoveryTrajectoryFollows
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) : Prop :=
  ∀ n, sys.Step (trajectory n) (trajectory (n + 1))

/-- Recovery status is eventually constant along a trajectory.  This says
nothing about convergence of the underlying states. -/
def EventuallyRecoveryStable
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) : Prop :=
  ∃ N, ∀ n, N ≤ n ->
    sys.status (trajectory n) = sys.status (trajectory N)

/-- The descent potential along a valid infinite trajectory never exceeds its
initial value. -/
theorem recoveryTrajectory_potential_le_initial
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    ∀ n, sys.potential (trajectory n) ≤ sys.potential (trajectory 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hBudget := sys.step_budget (hFollows n)
      omega

/-- If a later status differs from the initial status, then some adjacent edge
before it is a genuine status-changing edge. -/
theorem recoveryTrajectory_exists_adjacent_change_before
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State) {n : Nat}
    (hNe : sys.status (trajectory n) ≠ sys.status (trajectory 0)) :
    ∃ k, k < n ∧
      sys.status (trajectory k) ≠ sys.status (trajectory (k + 1)) := by
  induction n with
  | zero =>
      exact False.elim (hNe rfl)
  | succ n ih =>
      by_cases hLast :
          sys.status (trajectory n) = sys.status (trajectory (n + 1))
      · have hPrev :
            sys.status (trajectory n) ≠ sys.status (trajectory 0) := by
          intro hEq
          apply hNe
          calc
            sys.status (trajectory (n + 1)) = sys.status (trajectory n) := hLast.symm
            _ = sys.status (trajectory 0) := hEq
        obtain ⟨k, hk, hChange⟩ := ih hPrev
        exact ⟨k, by omega, hChange⟩
      · exact ⟨n, by omega, hLast⟩

/-- Zero remaining potential freezes recovery status forever along any valid
trajectory, even though the underlying states may continue to change. -/
theorem recoveryTrajectory_status_eq_initial_of_zero_potential
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (hZero : sys.potential (trajectory 0) = 0) :
    ∀ n, sys.status (trajectory n) = sys.status (trajectory 0) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hEq :
          sys.status (trajectory (n + 1)) = sys.status (trajectory n)
      · exact hEq.trans ih
      · have hChange :
            sys.status (trajectory n) ≠ sys.status (trajectory (n + 1)) := by
          intro h
          exact hEq h.symm
        have hLt := sys.potential_lt_of_status_change (hFollows n) hChange
        have hLe := recoveryTrajectory_potential_le_initial sys trajectory hFollows n
        omega

/-- Bounded-potential induction principle behind Gate 27. -/
theorem recoveryTrajectory_eventuallyStable_of_initialPotential_le
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory)
    (p : Nat)
    (hBound : sys.potential (trajectory 0) ≤ p) :
    EventuallyRecoveryStable sys trajectory := by
  induction p generalizing trajectory with
  | zero =>
      have hZero : sys.potential (trajectory 0) = 0 := by
        omega
      refine ⟨0, ?_⟩
      intro n hn
      simpa using
        recoveryTrajectory_status_eq_initial_of_zero_potential
          sys trajectory hFollows hZero n
  | succ p ih =>
      by_cases hAll :
          ∀ n, sys.status (trajectory n) = sys.status (trajectory 0)
      · refine ⟨0, ?_⟩
        intro n hn
        simpa using hAll n
      · have hExists :
            ∃ n, sys.status (trajectory n) ≠ sys.status (trajectory 0) :=
          Classical.not_forall.mp hAll
        obtain ⟨n, hNe⟩ := hExists
        obtain ⟨k, hk, hChange⟩ :=
          recoveryTrajectory_exists_adjacent_change_before sys trajectory hNe
        let tail : Nat -> State := fun j => trajectory (k + 1 + j)
        have hTailFollows : recoveryTrajectoryFollows sys tail := by
          intro j
          dsimp [tail]
          have hIndex : k + 1 + (j + 1) = (k + 1 + j) + 1 := by
            omega
          rw [hIndex]
          exact hFollows (k + 1 + j)
        have hKLe :
            sys.potential (trajectory k) ≤ sys.potential (trajectory 0) :=
          recoveryTrajectory_potential_le_initial sys trajectory hFollows k
        have hK1Lt :
            sys.potential (trajectory (k + 1)) < sys.potential (trajectory k) :=
          sys.potential_lt_of_status_change (hFollows k) hChange
        have hTailBound : sys.potential (tail 0) ≤ p := by
          dsimp [tail]
          omega
        obtain ⟨N, hN⟩ := ih tail hTailFollows hTailBound
        refine ⟨k + 1 + N, ?_⟩
        intro m hm
        let j := m - (k + 1)
        have hjEq : k + 1 + j = m := by
          dsimp [j]
          omega
        have hNj : N ≤ j := by
          dsimp [j]
          omega
        have hStable := hN j hNj
        dsimp [tail] at hStable
        rw [hjEq] at hStable
        exact hStable

/-- Main Gate-27 theorem: every infinite trajectory satisfying the Gate-26
finite-descent contract eventually stabilizes in recovery status. -/
theorem recoveryTrajectory_eventuallyRecoveryStable
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    EventuallyRecoveryStable sys trajectory := by
  exact recoveryTrajectory_eventuallyStable_of_initialPotential_le
    sys trajectory hFollows (sys.potential (trajectory 0)) (by omega)

/-- Equivalent operational consequence: genuine recovery changes cannot occur
arbitrarily late along a valid infinite trajectory. -/
theorem recoveryTrajectory_not_infinitely_often_changes
    {State : Type} (sys : RecoveryDescentSystem State)
    (trajectory : Nat -> State)
    (hFollows : recoveryTrajectoryFollows sys trajectory) :
    ¬ (∀ N, ∃ n, N ≤ n ∧
      sys.status (trajectory n) ≠ sys.status (trajectory (n + 1))) := by
  intro hInf
  obtain ⟨N, hStable⟩ :=
    recoveryTrajectory_eventuallyRecoveryStable sys trajectory hFollows
  obtain ⟨n, hn, hChange⟩ := hInf N
  have hN := hStable n hn
  have hN1 := hStable (n + 1) (by omega)
  apply hChange
  exact hN.trans hN1.symm

end PEL4