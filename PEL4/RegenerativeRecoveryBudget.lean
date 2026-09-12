import PEL4.FiniteEpistemicDescent

namespace PEL4

/-!
# Gate 34: regenerative recovery budgets

Gates 24--27 obtained finite Recovery-flip bounds from a potential that could
only be consumed. Gate 34 relaxes exactly that assumption. An update may create
new epistemic resource, but every created unit is charged explicitly to a
regeneration account.

The central invariant becomes

`changes incurred + final potential <= initial potential + total regeneration`.

Hence regeneration does not destroy accounting. It changes the conserved
quantity. Recovery oscillation may exceed the initial potential, but only by an
amount paid for by resource created along the path.
-/

/-- A Recovery update system in which a transition may regenerate finite
potential. `regeneration s t` is the amount of new resource credited to the
edge `s -> t`. -/
structure RecoveryRegenerativeSystem (State : Type) where
  status : State -> Bool
  potential : State -> Nat
  regeneration : State -> State -> Nat
  Step : State -> State -> Prop
  step_budget : ∀ {s t : State}, Step s t ->
    recoveryChangeCost (status s) (status t) + potential t ≤
      potential s + regeneration s t

/-- A finite successor list follows a regenerative update system. -/
def recoveryRegenerativeFollows
    {State : Type} (sys : RecoveryRegenerativeSystem State) :
    State -> List State -> Prop
  | _, [] => True
  | s, t :: rest =>
      sys.Step s t ∧ recoveryRegenerativeFollows sys t rest

/-- Number of Recovery-status changes along a finite regenerative path. -/
def recoveryRegenerativeChangeCountFrom
    {State : Type} (sys : RecoveryRegenerativeSystem State) :
    State -> List State -> Nat
  | _, [] => 0
  | s, t :: rest =>
      recoveryChangeCost (sys.status s) (sys.status t) +
        recoveryRegenerativeChangeCountFrom sys t rest

/-- Total resource regenerated along a finite path. -/
def recoveryRegenerationTotalFrom
    {State : Type} (sys : RecoveryRegenerativeSystem State) :
    State -> List State -> Nat
  | _, [] => 0
  | s, t :: rest =>
      sys.regeneration s t + recoveryRegenerationTotalFrom sys t rest

/-- Final state of a finite regenerative path. -/
def recoveryRegenerativeFinalStateFrom
    {State : Type} : State -> List State -> State
  | s, [] => s
  | _, t :: rest => recoveryRegenerativeFinalStateFrom t rest

/-- Main Gate-34 accounting law. New resource is not free: every unit appears
on the right-hand side as explicit regeneration. -/
theorem recoveryRegenerative_changeCount_add_finalPotential_le
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State)
    (hFollows : recoveryRegenerativeFollows sys start successors) :
    recoveryRegenerativeChangeCountFrom sys start successors +
        sys.potential
          (recoveryRegenerativeFinalStateFrom start successors) ≤
      sys.potential start +
        recoveryRegenerationTotalFrom sys start successors := by
  induction successors generalizing start with
  | nil =>
      simp [recoveryRegenerativeChangeCountFrom,
        recoveryRegenerationTotalFrom, recoveryRegenerativeFinalStateFrom]
  | cons next rest ih =>
      simp only [recoveryRegenerativeFollows] at hFollows
      have hHead := sys.step_budget hFollows.1
      have hTail := ih next hFollows.2
      simp only [recoveryRegenerativeChangeCountFrom,
        recoveryRegenerationTotalFrom, recoveryRegenerativeFinalStateFrom]
      omega

/-- Finite Recovery flips are bounded by initial resource plus all resource
regenerated along the path. -/
theorem recoveryRegenerative_changeCount_le_initial_add_regeneration
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State)
    (hFollows : recoveryRegenerativeFollows sys start successors) :
    recoveryRegenerativeChangeCountFrom sys start successors ≤
      sys.potential start + recoveryRegenerationTotalFrom sys start successors := by
  have h := recoveryRegenerative_changeCount_add_finalPotential_le
    sys start successors hFollows
  omega

/-- External finite regeneration cap. This is the form useful when the update
mechanism has a separately proved resource-creation budget `R`. -/
def RecoveryRegenerationWithin
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State) (R : Nat) : Prop :=
  recoveryRegenerationTotalFrom sys start successors ≤ R

/-- If at most `R` units can be regenerated, at most `initial + R` Recovery
flips can occur. -/
theorem recoveryRegenerative_changeCount_le_initial_add_budget
    {State : Type} (sys : RecoveryRegenerativeSystem State)
    (start : State) (successors : List State) (R : Nat)
    (hFollows : recoveryRegenerativeFollows sys start successors)
    (hRegen : RecoveryRegenerationWithin sys start successors R) :
    recoveryRegenerativeChangeCountFrom sys start successors ≤
      sys.potential start + R := by
  have h := recoveryRegenerative_changeCount_le_initial_add_regeneration
    sys start successors hFollows
  exact Nat.le_trans h (Nat.add_le_add_left hRegen _)

/-- Every ordinary Gate-26 descent system is the zero-regeneration special
case of Gate 34. -/
def RecoveryDescentSystem.toRegenerative
    {State : Type} (sys : RecoveryDescentSystem State) :
    RecoveryRegenerativeSystem State where
  status := sys.status
  potential := sys.potential
  regeneration := fun _ _ => 0
  Step := sys.Step
  step_budget := by
    intro s t hStep
    simpa using sys.step_budget hStep

/-- In the zero-regeneration embedding, total regenerated resource is zero. -/
@[simp] theorem RecoveryDescentSystem.toRegenerative_regenerationTotal
    {State : Type} (sys : RecoveryDescentSystem State)
    (start : State) (successors : List State) :
    recoveryRegenerationTotalFrom sys.toRegenerative start successors = 0 := by
  induction successors generalizing start with
  | nil => simp [recoveryRegenerationTotalFrom]
  | cons next rest ih =>
      simp [recoveryRegenerationTotalFrom, RecoveryDescentSystem.toRegenerative,
        ih next]

/-- Gate 26 is recovered as the no-regeneration boundary of Gate 34. -/
theorem recoveryDescent_changeCount_le_via_regenerative
    {State : Type} (sys : RecoveryDescentSystem State)
    (start : State) (successors : List State)
    (hFollows : recoveryDescentFollows sys start successors) :
    recoveryChangeCountFrom sys start successors ≤ sys.potential start := by
  exact recoveryDescent_changeCount_le_initialPotential
    sys start successors hFollows

/-! ## Sharp regeneration witness -/

inductive Gate34State where
  | start
  | regenerated
  | finish
  deriving DecidableEq, Repr

/-- A tiny system in which one newly generated resource unit funds one extra
Recovery flip beyond the initial potential. -/
def gate34RegenerativeSystem : RecoveryRegenerativeSystem Gate34State where
  status
    | .start => true
    | .regenerated => false
    | .finish => true
  potential
    | .start => 1
    | .regenerated => 1
    | .finish => 0
  regeneration s t :=
    if s = .start ∧ t = .regenerated then 1 else 0
  Step := fun s t =>
    (s = .start ∧ t = .regenerated) ∨
    (s = .regenerated ∧ t = .finish)
  step_budget := by
    intro s t hStep
    rcases hStep with hFirst | hSecond
    · rcases hFirst with ⟨rfl, rfl⟩
      decide
    · rcases hSecond with ⟨rfl, rfl⟩
      decide

/-- The witness path is valid. -/
theorem gate34_regenerative_path_follows :
    recoveryRegenerativeFollows gate34RegenerativeSystem Gate34State.start
      [Gate34State.regenerated, Gate34State.finish] := by
  decide +kernel

/-- The path contains two Recovery flips despite starting with potential one. -/
theorem gate34_regeneration_funds_extra_flip :
    recoveryRegenerativeChangeCountFrom gate34RegenerativeSystem
      Gate34State.start [Gate34State.regenerated, Gate34State.finish] = 2 := by
  decide +kernel

/-- Exactly one resource unit is regenerated. -/
theorem gate34_regeneration_total_is_one :
    recoveryRegenerationTotalFrom gate34RegenerativeSystem
      Gate34State.start [Gate34State.regenerated, Gate34State.finish] = 1 := by
  decide +kernel

/-- The general bound is sharp on the witness: `2 = 1 + 1`. -/
theorem gate34_regenerative_bound_is_sharp :
    recoveryRegenerativeChangeCountFrom gate34RegenerativeSystem
        Gate34State.start [Gate34State.regenerated, Gate34State.finish] =
      gate34RegenerativeSystem.potential Gate34State.start +
        recoveryRegenerationTotalFrom gate34RegenerativeSystem
          Gate34State.start [Gate34State.regenerated, Gate34State.finish] := by
  decide +kernel

/-- Regeneration can make a future flip possible even when the pre-edge
potential alone would not pay for both the flip and the remaining potential. -/
theorem gate34_regeneration_is_genuinely_used :
    recoveryChangeCost
        (gate34RegenerativeSystem.status Gate34State.start)
        (gate34RegenerativeSystem.status Gate34State.regenerated) +
      gate34RegenerativeSystem.potential Gate34State.regenerated >
      gate34RegenerativeSystem.potential Gate34State.start := by
  decide +kernel

end PEL4
