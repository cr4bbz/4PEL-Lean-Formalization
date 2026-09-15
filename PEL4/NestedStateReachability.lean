import PEL4.RationalEpistemicSelfTrust

namespace PEL4

/-!
# Gate 105: reachability of nested epistemic states

Gate 103 introduced the product state `(world, model) : FDEValue × FDEValue`, and
Gate 104 attached a controller to selected witnesses. Gate 105 turns that static
product into a finite transition system.

The transition system is deliberately idealized: a diagnostic event may update
exactly one coordinate while leaving the other untouched. This gives us a clean
baseline for asking which of the sixteen canonical nested 4PEL states are
reachable before later gates impose costs, observation kernels, and rationality
constraints.
-/

/-- A diagnostic event updates either the first-order world verdict or the
second-order model verdict. -/
inductive Gate105Event where
  | worldVerdict (value : FDEValue)
  | modelVerdict (value : FDEValue)
  deriving Repr

/-- One coordinate-local epistemic transition. -/
def gate105Step (state : Gate103NestedStatus) (event : Gate105Event) :
    Gate103NestedStatus :=
  match event with
  | .worldVerdict value => { state with world := value }
  | .modelVerdict value => { state with model := value }

/-- Execute a finite diagnostic path. -/
def gate105Run (start : Gate103NestedStatus) (events : List Gate105Event) :
    Gate103NestedStatus :=
  events.foldl gate105Step start

/-- Ordinary finite-path reachability in the Gate-105 transition system. -/
def gate105Reachable (from to : Gate103NestedStatus) : Prop :=
  ∃ events : List Gate105Event, gate105Run from events = to

/-- The four canonical 4PEL verdicts. -/
def gate105Values : List FDEValue :=
  [FDEValue.T, FDEValue.F, FDEValue.B, FDEValue.N]

/-- The canonical `4 × 4` nested epistemic state space. -/
def gate105CanonicalStates : List Gate103NestedStatus :=
  gate105Values.flatMap (fun world =>
    gate105Values.map (fun model => { world := world, model := model }))

/-- A world diagnostic leaves second-order model status invariant. -/
theorem gate105_world_update_preserves_model
    (state : Gate103NestedStatus) (value : FDEValue) :
    (gate105Step state (.worldVerdict value)).model = state.model := by
  rfl

/-- A model diagnostic leaves first-order world status invariant. -/
theorem gate105_model_update_preserves_world
    (state : Gate103NestedStatus) (value : FDEValue) :
    (gate105Step state (.modelVerdict value)).world = state.world := by
  rfl

/-- Two coordinate-local diagnostics can install any requested nested status. -/
theorem gate105_two_step_target
    (from : Gate103NestedStatus) (world model : FDEValue) :
    gate105Run from [.worldVerdict world, .modelVerdict model] =
      { world := world, model := model } := by
  rfl

/-- The canonical product really contains sixteen entries. -/
theorem gate105_sixteen_canonical_states :
    gate105CanonicalStates.length = 16 := by
  native_decide

/-- None of the sixteen canonical nested statuses collapse extensionally. -/
theorem gate105_canonical_states_are_distinct :
    gate105CanonicalStates.Nodup := by
  native_decide

/-- Strong-connectivity witness: under ideal coordinate-local diagnostics, every
nested epistemic state can reach every other in at most two updates. -/
theorem gate105_any_state_reaches_any_state
    (from target : Gate103NestedStatus) :
    gate105Reachable from target := by
  refine ⟨[.worldVerdict target.world, .modelVerdict target.model], ?_⟩
  rcases target with ⟨world, model⟩
  exact gate105_two_step_target from world model

/-- In particular, every canonical state is reachable from the trusted-truth
state used by Gates 103 and 104. -/
theorem gate105_all_canonical_states_reachable_from_trusted_truth
    (target : Gate103NestedStatus)
    (h : target ∈ gate105CanonicalStates) :
    gate105Reachable gate103TrustedTruth target := by
  exact gate105_any_state_reaches_any_state gate103TrustedTruth target

/-- A model gap can be repaired without changing the already-supported world
coordinate. -/
theorem gate105_model_gap_has_repair_path :
    gate105Run gate103TruthWithModelGap [.modelVerdict FDEValue.T] =
      gate103TrustedTruth := by
  native_decide

/-- A model conflict likewise has a coordinate-local route back to strict model
support while preserving the world verdict. -/
theorem gate105_model_conflict_has_repair_path :
    gate105Run gate103TruthWithModelConflict [.modelVerdict FDEValue.T] =
      gate103TrustedTruth := by
  native_decide

/-- Main Gate-105 result: the Gate-103 product is not merely a collection of
independent witnesses. Under one explicit coordinate-local transition system,
the sixteen canonical nested states are distinct and the state graph is strongly
connected. -/
theorem gate105_nested_state_reachability :
    gate105CanonicalStates.length = 16 ∧
    gate105CanonicalStates.Nodup ∧
    (∀ from target : Gate103NestedStatus, gate105Reachable from target) := by
  exact ⟨gate105_sixteen_canonical_states,
    gate105_canonical_states_are_distinct,
    gate105_any_state_reaches_any_state⟩

/-!
## Gate-105 interpretation boundary

The strong-connectivity theorem is conditional on an intentionally permissive
transition model: diagnostic events can directly install any four-valued verdict
on either coordinate. It therefore establishes a structural possibility result,
not that a real evidence process can generate every transition, nor that every
transition is rational or equally costly. Gates 106 and 107 will attack exactly
those assumptions by adding decision costs and testing whether the four-valued
abstraction preserves enough information for optimal control.
-/

end PEL4
