import PEL4.SelfCorrectionLiveness

namespace PEL4

/-!
# Gate 110: observational aliasing limits self-correction

Gate 109 proved a liveness theorem under an ideal repair-success assumption: if a
nonclassical coordinate can always be repaired when selected, the two-coordinate
nested epistemic state reaches a classical region within two repair steps.

Gate 110 removes the hidden informational assumption behind that oracle. Two
possible worlds may require opposite classical verdicts while producing exactly
the same available observation. Any repair policy restricted to that observation
channel must then return the same verdict in both worlds, so it cannot be correct
in both.

This is a finite identifiability counterexample. The obstruction is not lack of
computation or failure of the Gate-109 ranking argument. It is observational
aliasing: the evidence channel itself does not distinguish the target states.
-/

/-- Two hidden worlds that require opposite strict verdicts. -/
inductive Gate110HiddenWorld where
  | positive
  | negative
  deriving DecidableEq, Repr

/-- The deliberately impoverished observation channel has only one reading. -/
inductive Gate110Observation where
  | aliased
  deriving DecidableEq, Repr

/-- Both hidden worlds generate the same available observation. -/
def gate110Observe : Gate110HiddenWorld → Gate110Observation
  | .positive => .aliased
  | .negative => .aliased

/-- The correct strict 4PEL verdict differs across the hidden worlds. -/
def gate110Target : Gate110HiddenWorld → FDEValue
  | .positive => FDEValue.T
  | .negative => FDEValue.F

/-- A repair policy is evidence-restricted when it can depend only on the
observation supplied by `gate110Observe`. -/
abbrev Gate110RepairPolicy := Gate110Observation → FDEValue

/-- Correctness of an evidence-restricted repair policy at one hidden world. -/
def gate110CorrectAt (policy : Gate110RepairPolicy)
    (world : Gate110HiddenWorld) : Prop :=
  policy (gate110Observe world) = gate110Target world

/-- The two hidden worlds are observationally indistinguishable. -/
theorem gate110_worlds_are_observationally_aliased :
    gate110Observe .positive = gate110Observe .negative := by
  rfl

/-- Nevertheless, the worlds require opposite strict verdicts. -/
theorem gate110_aliased_worlds_require_different_targets :
    gate110Target .positive ≠ gate110Target .negative := by
  native_decide

/-- No policy that sees only the aliased observation can classify both hidden
worlds correctly. -/
theorem gate110_no_evidence_restricted_policy_is_uniformly_correct
    (policy : Gate110RepairPolicy) :
    ¬ (gate110CorrectAt policy .positive ∧
       gate110CorrectAt policy .negative) := by
  intro hCorrect
  rcases hCorrect with ⟨hPositive, hNegative⟩
  have hSameOutput :
      policy (gate110Observe .positive) =
        policy (gate110Observe .negative) :=
    congrArg policy gate110_worlds_are_observationally_aliased
  have hTargetsEqual :
      gate110Target .positive = gate110Target .negative := by
    calc
      gate110Target .positive = policy (gate110Observe .positive) := hPositive.symm
      _ = policy (gate110Observe .negative) := hSameOutput
      _ = gate110Target .negative := hNegative
  exact gate110_aliased_worlds_require_different_targets hTargetsEqual

/-- Equivalently, every evidence-restricted repair policy fails in at least one
of the two hidden worlds. -/
theorem gate110_every_policy_fails_some_aliased_world
    (policy : Gate110RepairPolicy) :
    ∃ world : Gate110HiddenWorld, ¬ gate110CorrectAt policy world := by
  by_cases hPositive : gate110CorrectAt policy .positive
  · refine ⟨.negative, ?_⟩
    intro hNegative
    exact gate110_no_evidence_restricted_policy_is_uniformly_correct policy
      ⟨hPositive, hNegative⟩
  · exact ⟨.positive, hPositive⟩

/-- Both hidden worlds present the controller with the same nested visible state:
world status `N` under a trusted model `T`. -/
def gate110VisibleState (_world : Gate110HiddenWorld) : Gate103NestedStatus :=
  gate103WorldGapTrustedModel

/-- The nested 4PEL state itself therefore cannot distinguish the two hidden
worlds in this witness. -/
theorem gate110_same_visible_nested_state :
    gate110VisibleState .positive = gate110VisibleState .negative := by
  rfl

/-- Gate 109's ideal repair controller does exactly what its liveness theorem
promises on the aliased negative world: it exits the gap and reaches a classical
state. But because its repair oracle installs `T`, the result is the wrong target
for the hidden negative world. Thus classicalization is weaker than correctness. -/
theorem gate110_gate109_liveness_does_not_imply_truth :
    gate109Stable
      (gate109RepairStep (gate109RepairStep (gate110VisibleState .negative))) ∧
    (gate109RepairStep (gate110VisibleState .negative)).world ≠
      gate110Target .negative := by
  constructor
  · exact gate109_two_steps_reach_stable (gate110VisibleState .negative)
  · native_decide

/-- Main Gate-110 no-go theorem: observational aliasing separates repair liveness
from truth-guaranteeing self-correction. The ideal Gate-109 controller still
terminates, yet no policy restricted to the available observation can be correct
in both aliased worlds. -/
theorem gate110_observational_aliasing_limit :
    gate110Observe .positive = gate110Observe .negative ∧
    gate110Target .positive ≠ gate110Target .negative ∧
    (∀ policy : Gate110RepairPolicy,
      ∃ world : Gate110HiddenWorld, ¬ gate110CorrectAt policy world) ∧
    gate109Stable
      (gate109RepairStep (gate109RepairStep (gate110VisibleState .negative))) := by
  exact ⟨gate110_worlds_are_observationally_aliased,
    gate110_aliased_worlds_require_different_targets,
    gate110_every_policy_fails_some_aliased_world,
    (gate110_gate109_liveness_does_not_imply_truth).1⟩

/-!
## Gate-110 interpretation boundary

The theorem is not a universal impossibility theorem for learning or knowledge.
It is conditional on the explicit observation map above. If the agent gains a new
measurement, intervention, experiment, or side channel that separates the hidden
worlds, the no-go result no longer applies.

What is verified is the structural point needed after Gate 109: termination of an
epistemic repair process does not by itself imply successful identification of
truth. A controller can become classically decisive and still be wrong when its
available evidence aliases distinct truth conditions.

This suggests the next research move: replace passive repair by active
identification. A later gate can ask whether an additional experiment can break
the alias and restore a truth-guaranteeing repair policy.
-/

end PEL4
