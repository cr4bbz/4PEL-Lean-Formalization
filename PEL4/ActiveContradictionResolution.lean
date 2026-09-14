import PEL4.FourValuedControlBridge

namespace PEL4

/-!
# Gate 77: active contradiction resolution

Gate 76 controlled an epistemic gap `N`. Gate 77 treats the dual nonclassical
problem: a glut `B`, where positive and negative evidence are both strong.

A genuine glut requires two independent support channels rather than a single
probability distribution over exclusive alternatives. The finite witness below
starts with `4/5` support on both sides. A resolving experiment has two equiprobable
outcomes, each of which suppresses one support channel and strengthens the other.
-/

structure Gate77EvidenceState where
  posSupport : Rat
  negSupport : Rat
  deriving DecidableEq, Repr

/-- Four-valued classification with independent `3/4` support thresholds. -/
def gate77Status (state : Gate77EvidenceState) : FDEValue :=
  { pos := decide ((3 : Rat) / 4 ≤ state.posSupport)
    neg := decide ((3 : Rat) / 4 ≤ state.negSupport) }

/-- Initial contradictory evidence state. -/
def gate77ConflictState : Gate77EvidenceState :=
  { posSupport := (4 : Rat) / 5
    negSupport := (4 : Rat) / 5 }

inductive Gate77ResolutionObservation where
  | positiveWins
  | negativeWins
  deriving DecidableEq, Repr

/-- The resolving experiment produces one-sided high support. -/
def gate77ResolvedState
    (observation : Gate77ResolutionObservation) : Gate77EvidenceState :=
  match observation with
  | .positiveWins =>
      { posSupport := (9 : Rat) / 10, negSupport := (1 : Rat) / 10 }
  | .negativeWins =>
      { posSupport := (1 : Rat) / 10, negSupport := (9 : Rat) / 10 }

/-- Utility rewards strict classical resolution (`T` or `F`) and gives zero to
remaining `B` or `N` states. -/
def gate77ResolutionUtility (state : Gate77EvidenceState) : Rat :=
  if gate77Status state = FDEValue.T ∨ gate77Status state = FDEValue.F then 1 else 0

/-- The experiment costs `1/5` and its two outcomes are equiprobable. -/
def gate77ResolveQ : Rat :=
  -((1 : Rat) / 5) +
    (1 : Rat) / 2 * gate77ResolutionUtility (gate77ResolvedState .positiveWins) +
    (1 : Rat) / 2 * gate77ResolutionUtility (gate77ResolvedState .negativeWins)

inductive Gate77Decision where
  | stop
  | resolveConflict
  deriving DecidableEq, Repr

/-- Stop on ties; otherwise buy the resolving experiment when its net value is
strictly larger than accepting the current state. -/
def gate77ChooseDecision : Gate77Decision :=
  if gate77ResolveQ > gate77ResolutionUtility gate77ConflictState then
    .resolveConflict
  else
    .stop

/-- The initial evidence state is a genuine four-valued glut. -/
theorem gate77_initial_state_is_glut :
    gate77Status gate77ConflictState = FDEValue.B := by
  native_decide

/-- Positive resolution produces strict truth. -/
theorem gate77_positive_resolution_is_true :
    gate77Status (gate77ResolvedState .positiveWins) = FDEValue.T := by
  native_decide

/-- Negative resolution produces strict falsity. -/
theorem gate77_negative_resolution_is_false :
    gate77Status (gate77ResolvedState .negativeWins) = FDEValue.F := by
  native_decide

/-- Stopping in the glut has zero resolution utility. -/
theorem gate77_glut_stop_utility_zero :
    gate77ResolutionUtility gate77ConflictState = 0 := by
  native_decide

/-- The resolving experiment has positive net value `4/5`. -/
theorem gate77_resolution_q_value :
    gate77ResolveQ = (4 : Rat) / 5 := by
  native_decide

/-- Therefore the optimal local action is to pay for contradiction resolution. -/
theorem gate77_policy_resolves_conflict :
    gate77ChooseDecision = .resolveConflict := by
  native_decide

/-- Every possible experiment outcome exits the glut into a strict classical
state. -/
theorem gate77_resolution_always_classical
    (observation : Gate77ResolutionObservation) :
    gate77Status (gate77ResolvedState observation) = FDEValue.T ∨
    gate77Status (gate77ResolvedState observation) = FDEValue.F := by
  cases observation <;> native_decide

/-- Main Gate-77 theorem: contradiction itself becomes an object of active
control. With an explicit utility for classical resolution and a positive sensing
cost, the rational policy buys an experiment that transforms `B` into `T` or `F`.
-/
theorem gate77_active_contradiction_resolution :
    gate77Status gate77ConflictState = FDEValue.B ∧
    gate77ResolutionUtility gate77ConflictState = 0 ∧
    gate77ResolveQ = (4 : Rat) / 5 ∧
    gate77ChooseDecision = .resolveConflict ∧
    (∀ observation,
      gate77Status (gate77ResolvedState observation) = FDEValue.T ∨
      gate77Status (gate77ResolvedState observation) = FDEValue.F) := by
  exact ⟨gate77_initial_state_is_glut,
    gate77_glut_stop_utility_zero,
    gate77_resolution_q_value,
    gate77_policy_resolves_conflict,
    gate77_resolution_always_classical⟩

/-!
## Gate-77 boundary

The utility of strict classical resolution is declared rather than derived from
a universal epistemic axiology, and the resolving experiment is an explicit
finite witness. The important structural result is narrower: 4PEL contradiction
need not be treated as a terminal defect or as explosion. It can be represented
as a controllable epistemic state for which acquiring discriminating evidence has
positive decision value.
-/

end PEL4
