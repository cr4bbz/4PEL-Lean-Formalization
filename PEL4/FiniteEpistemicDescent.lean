import PEL4.RecoveryCoordinateBudget

namespace PEL4

/-!
# Gate 26: abstract finite epistemic descent

Gate 25 showed that conditionalization consumes a finite duplicate-free
coordinate resource whenever compositional recovery changes status.  This gate
separates that semantic fact from the counting argument.

The abstraction below knows nothing about conditionalization, probability,
modal syntax, or even 4PEL.  It requires only:

* a Boolean status attached to each state,
* a natural-valued finite potential,
* an update relation, and
* a local descent contract saying that every status change costs one unit of
  potential while the remaining potential cannot increase enough to violate
  the one-step budget.

Any update system satisfying that contract inherits a uniform finite bound on
status changes along every finite path.  Gate 25 is then recovered as one
verified instance of the local contract.
-/

/-- Unit cost of changing a Boolean recovery status. -/
def recoveryChangeCost (before after : Bool) : Nat :=
  if before = after then 0 else 1

@[simp] theorem recoveryChangeCost_self (b : Bool) :
    recoveryChangeCost b b = 0 := by
  simp [recoveryChangeCost]

/-- A genuine status change costs exactly one unit. -/
theorem recoveryChangeCost_eq_one_of_ne
    {before after : Bool} (h : before ≠ after) :
    recoveryChangeCost before after = 1 := by
  simp [recoveryChangeCost, h]

/-- Abstract finite-descent contract for an arbitrary update relation. -/
structure RecoveryDescentSystem (State : Type) where
  status : State -> Bool
  potential : State -> Nat
  Step : State -> State -> Prop
  step_budget : ∀ {s t : State}, Step s t ->
    recoveryChangeCost (status s) (status t) + potential t ≤ potential s

/-- A finite list of successor states follows the abstract update relation from
an explicit starting state. -/
def recoveryDescentFollows
    {State : Type} (sys : RecoveryDescentSystem State) :
    State -> List State -> Prop
  | _, [] => True
  | s, t :: rest => sys.Step s t ∧ recoveryDescentFollows sys t rest

/-- Number of status-changing edges along an abstract finite path. -/
def recoveryChangeCountFrom
    {State : Type} (sys : RecoveryDescentSystem State) :
    State -> List State -> Nat
  | _, [] => 0
  | s, t :: rest =>
      recoveryChangeCost (sys.status s) (sys.status t) +
        recoveryChangeCountFrom sys t rest

/-- Final state reached after following a finite successor list. -/
def recoveryFinalStateFrom
    {State : Type} : State -> List State -> State
  | s, [] => s
  | _, t :: rest => recoveryFinalStateFrom t rest

/-- Every genuine status-changing step strictly decreases the natural-valued
potential. -/
theorem RecoveryDescentSystem.potential_lt_of_status_change
    {State : Type} (sys : RecoveryDescentSystem State)
    {s t : State} (hStep : sys.Step s t)
    (hChange : sys.status s ≠ sys.status t) :
    sys.potential t < sys.potential s := by
  have hBudget := sys.step_budget hStep
  have hCost := recoveryChangeCost_eq_one_of_ne hChange
  rw [hCost] at hBudget
  omega

/-- Main abstract Gate-26 invariant: changes already incurred plus unused final
potential never exceed the initial potential. -/
theorem recoveryDescent_changeCount_add_finalPotential_le
    {State : Type} (sys : RecoveryDescentSystem State)
    (start : State) (successors : List State)
    (hFollows : recoveryDescentFollows sys start successors) :
    recoveryChangeCountFrom sys start successors +
        sys.potential (recoveryFinalStateFrom start successors) ≤
      sys.potential start := by
  induction successors generalizing start with
  | nil =>
      simp [recoveryChangeCountFrom, recoveryFinalStateFrom]
  | cons next rest ih =>
      simp only [recoveryDescentFollows] at hFollows
      have hHead := sys.step_budget hFollows.1
      have hTail := ih next hFollows.2
      simp only [recoveryChangeCountFrom, recoveryFinalStateFrom]
      omega

/-- Uniform finite-flip theorem.  Path length is irrelevant: every finite path
contains at most the initial number of resource units in status changes. -/
theorem recoveryDescent_changeCount_le_initialPotential
    {State : Type} (sys : RecoveryDescentSystem State)
    (start : State) (successors : List State)
    (hFollows : recoveryDescentFollows sys start successors) :
    recoveryChangeCountFrom sys start successors ≤ sys.potential start := by
  have h := recoveryDescent_changeCount_add_finalPotential_le
    sys start successors hFollows
  omega

/-- Once the potential is exhausted, no finite continuation satisfying the
contract can contain another status change. -/
theorem recoveryDescent_no_changes_of_zero_potential
    {State : Type} (sys : RecoveryDescentSystem State)
    (start : State) (successors : List State)
    (hFollows : recoveryDescentFollows sys start successors)
    (hZero : sys.potential start = 0) :
    recoveryChangeCountFrom sys start successors = 0 := by
  have h := recoveryDescent_changeCount_le_initialPotential
    sys start successors hFollows
  omega

/-- Minimal status/potential snapshot used to expose the abstract resource
contract independently of the underlying epistemic state. -/
structure RecoveryBudgetSnapshot where
  status : Bool
  potential : Nat
  deriving DecidableEq, Repr

/-- Canonical abstract system on budget snapshots.  An edge is permitted
exactly when it satisfies the one-step descent inequality. -/
def recoveryBudgetSnapshotSystem :
    RecoveryDescentSystem RecoveryBudgetSnapshot where
  status := RecoveryBudgetSnapshot.status
  potential := RecoveryBudgetSnapshot.potential
  Step := fun s t =>
    recoveryChangeCost s.status t.status + t.potential ≤ s.potential
  step_budget := by
    intro s t h
    exact h

/-- Gate-25 coordinate accounting packaged as an abstract status/potential
snapshot. -/
def recoveryCoordinateSnapshot
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W) : RecoveryBudgetSnapshot :=
  { status := recoveryStatusOnBool m roots phi
    potential := recoveryCoordinatePotential m roots phi scope }

/-- Bridge theorem: every admissible conditionalization edge with a
concentrated cumulative scope is an instance of the abstract Gate-26 descent
contract.  The generic counting proof therefore no longer depends on the
internals of conditionalization. -/
theorem conditionalization_recoveryCoordinateSnapshot_step
    {W Ag Atom : Type} [DecidableEq W] [DecidableEq Ag]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (roots : FiniteSet W)
    (phi : ModalFormula Atom Ag)
    (scope : Ag -> W -> FiniteSet W)
    (hConcentrated : ∀ i w,
      LocalMeasureConcentratedOn m i w (scope i w)) :
    recoveryBudgetSnapshotSystem.Step
      (recoveryCoordinateSnapshot m roots phi scope)
      (recoveryCoordinateSnapshot (conditionalize m E hAdm) roots phi
        (nextRecoveryScope m E scope)) := by
  simpa [recoveryBudgetSnapshotSystem, recoveryCoordinateSnapshot,
    recoveryChangeCost] using
    recoveryChangeIndicator_add_nextCoordinatePotential_le
      m hIntegrity E hAdm roots phi scope hConcentrated

/-- Tiny executable sanity model: two status flips consume a potential of two
exactly, matching the PEL-4 robot intuition. -/
def gate26RobotStart : RecoveryBudgetSnapshot :=
  { status := true, potential := 2 }

def gate26RobotMiddle : RecoveryBudgetSnapshot :=
  { status := false, potential := 1 }

def gate26RobotEnd : RecoveryBudgetSnapshot :=
  { status := true, potential := 0 }

theorem gate26_robot_path_follows :
    recoveryDescentFollows recoveryBudgetSnapshotSystem gate26RobotStart
      [gate26RobotMiddle, gate26RobotEnd] := by
  simp [recoveryDescentFollows, recoveryBudgetSnapshotSystem,
    recoveryChangeCost, gate26RobotStart, gate26RobotMiddle, gate26RobotEnd]

theorem gate26_robot_two_flips :
    recoveryChangeCountFrom recoveryBudgetSnapshotSystem gate26RobotStart
      [gate26RobotMiddle, gate26RobotEnd] = 2 := by
  decide +kernel

theorem gate26_robot_exhausts_budget :
    recoveryChangeCountFrom recoveryBudgetSnapshotSystem gate26RobotStart
        [gate26RobotMiddle, gate26RobotEnd] +
      recoveryBudgetSnapshotSystem.potential
        (recoveryFinalStateFrom gate26RobotStart
          [gate26RobotMiddle, gate26RobotEnd]) =
      recoveryBudgetSnapshotSystem.potential gate26RobotStart := by
  decide +kernel

end PEL4
