import PEL4.FiniteUpdateRecovery

namespace PEL4

/-!
# Gate 20: finite bounds for cumulative evidence-scope shrinkage

Successive conditionalizations restrict a local accessibility scope by the
worlds that positively support the next evidence formula.  The evidence
formula may depend on the posterior model produced by every preceding step,
so the resulting scope descent is dependent in the same sense as the update
trace from Gate 19.

This gate separates two claims that must not be conflated:

* every fixed local cumulative scope can shrink strictly only finitely often;
* a global bound on changes of compositional recovery needs an additional
  construction connecting all recovery-relevant belief nodes to finitely many
  such local descents.

The first claim is proved below with the sharp budget supplied by the initial
scope cardinality.  The second does not yet follow from the current formal
vocabulary: it contains no compiler enumerating all belief nodes reachable
from a formula and no stuttering theorem connecting those nodes to recovery.
-/

/-- A finite sequence of cumulative evidence restrictions.  Its index records
the current scope, so every successor starts at the actual intersection
produced by the preceding restriction. -/
inductive FiniteEvidenceScopeDescent
    {W : Type} [DecidableEq W] : FiniteSet W -> Type where
  | nil (scope : FiniteSet W) : FiniteEvidenceScopeDescent scope
  | step (scope evidence : FiniteSet W)
      (tail : FiniteEvidenceScopeDescent
        (intersectWorlds scope evidence)) :
      FiniteEvidenceScopeDescent scope

namespace FiniteEvidenceScopeDescent

/-- Number of evidence restrictions in the descent. -/
def length
    {W : Type} [DecidableEq W] {scope : FiniteSet W} :
    FiniteEvidenceScopeDescent scope -> Nat
  | .nil _ => 0
  | .step _ _ tail => tail.length + 1

/-- The cumulative scope after the final restriction. -/
def finalScope
    {W : Type} [DecidableEq W] {scope : FiniteSet W} :
    FiniteEvidenceScopeDescent scope -> FiniteSet W
  | .nil scope => scope
  | .step _ _ tail => tail.finalScope

/-- Number of steps at which the cumulative scope loses at least one world. -/
def strictShrinkCount
    {W : Type} [DecidableEq W] {scope : FiniteSet W} :
    FiniteEvidenceScopeDescent scope -> Nat
  | .nil _ => 0
  | .step scope evidence tail =>
      if (intersectWorlds scope evidence).length < scope.length then
        tail.strictShrinkCount + 1
      else
        tail.strictShrinkCount

/-- Intersecting a finite scope cannot increase its list length. -/
theorem intersectWorlds_length_le
    {W : Type} [DecidableEq W]
    (scope evidence : FiniteSet W) :
    (intersectWorlds scope evidence).length <= scope.length := by
  unfold intersectWorlds
  exact List.length_filter_le _ _

/-- Every strict restriction consumes at least one unit of the initial scope
budget.  Keeping the final cardinality in the statement gives a stronger
result than the bare count bound. -/
theorem finalScope_length_add_strictShrinkCount_le
    {W : Type} [DecidableEq W] {scope : FiniteSet W}
    (descent : FiniteEvidenceScopeDescent scope) :
    descent.finalScope.length + descent.strictShrinkCount <= scope.length := by
  induction descent with
  | nil _ => simp [finalScope, strictShrinkCount]
  | step scope evidence tail ih =>
      simp only [finalScope, strictShrinkCount]
      split
      · omega
      · have hLength := intersectWorlds_length_le scope evidence
        omega

/-- A fixed local cumulative scope can shrink strictly at most as many times
as it initially contains worlds. -/
theorem strictShrinkCount_le_initialLength
    {W : Type} [DecidableEq W] {scope : FiniteSet W}
    (descent : FiniteEvidenceScopeDescent scope) :
    descent.strictShrinkCount <= scope.length := by
  have h := finalScope_length_add_strictShrinkCount_le descent
  omega

/-- Strict shrinkage also cannot occur more often than there are update
steps. -/
theorem strictShrinkCount_le_length
    {W : Type} [DecidableEq W] {scope : FiniteSet W}
    (descent : FiniteEvidenceScopeDescent scope) :
    descent.strictShrinkCount <= descent.length := by
  induction descent with
  | nil _ => simp [strictShrinkCount, length]
  | step scope evidence tail ih =>
      simp only [strictShrinkCount, length]
      split <;> omega

end FiniteEvidenceScopeDescent

namespace FiniteConditionalizationTrace

/-- Compile a dependent conditionalization trace into the cumulative evidence
scope seen at one fixed agent/world pair, starting from an arbitrary scope.
Later evidence extensions are evaluated in their actual posterior source
models. -/
def evidenceScopeDescentFrom
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom} :
    (trace : FiniteConditionalizationTrace m) ->
    (i : Ag) -> (w : W) -> (scope : FiniteSet W) ->
      FiniteEvidenceScopeDescent scope
  | .nil _, _, _, scope => .nil scope
  | .step m E _ tail, i, w, scope =>
      .step scope (conditionalizationEvidenceEvent m.toModel i w E)
        (evidenceScopeDescentFrom tail i w
          (intersectWorlds scope
            (conditionalizationEvidenceEvent m.toModel i w E)))

/-- The local cumulative evidence descent begins with the accessibility scope
of the initial model. -/
def evidenceScopeDescent
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (i : Ag) (w : W) :
    FiniteEvidenceScopeDescent (m.toModel.R i w) :=
  evidenceScopeDescentFrom trace i w (m.toModel.R i w)

/-- Compiling a trace preserves the number of update edges. -/
theorem evidenceScopeDescentFrom_length
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (i : Ag) (w : W) (scope : FiniteSet W) :
    (evidenceScopeDescentFrom trace i w scope).length = trace.length := by
  induction trace generalizing scope with
  | nil _ => rfl
  | step m E hAdm tail ih =>
      simp [evidenceScopeDescentFrom,
        FiniteEvidenceScopeDescent.length, length, ih]

/-- Gate-20 local bound: along any admissible finite update trace, strict
cumulative evidence shrinkage at a fixed belief site is bounded both by the
trace length and by the initial accessibility-scope length. -/
theorem localEvidenceStrictShrinkCount_bounds
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (i : Ag) (w : W) :
    (evidenceScopeDescent trace i w).strictShrinkCount <= trace.length ∧
      (evidenceScopeDescent trace i w).strictShrinkCount <=
        (m.toModel.R i w).length := by
  constructor
  · rw [← evidenceScopeDescentFrom_length trace i w (m.toModel.R i w)]
    exact FiniteEvidenceScopeDescent.strictShrinkCount_le_length _
  · exact FiniteEvidenceScopeDescent.strictShrinkCount_le_initialLength _

/-- The stronger budget statement records how many worlds remain after the
trace as well as how many strict restrictions occurred. -/
theorem localEvidenceFinalScope_budget
    {W Ag Atom : Type} [DecidableEq W]
    {m : StrongProbabilityModel W Ag Atom}
    (trace : FiniteConditionalizationTrace m)
    (i : Ag) (w : W) :
    (evidenceScopeDescent trace i w).finalScope.length +
        (evidenceScopeDescent trace i w).strictShrinkCount <=
      (m.toModel.R i w).length :=
  FiniteEvidenceScopeDescent.finalScope_length_add_strictShrinkCount_le _

end FiniteConditionalizationTrace

/-! ## Sharpness and the Gate-19 loss/return trace -/

inductive Gate20World where
  | a | b | c
  deriving DecidableEq

/-- A three-world scope that loses exactly one world at every restriction. -/
def gate20SharpDescent :
    FiniteEvidenceScopeDescent
      ([Gate20World.a, .b, .c] : FiniteSet Gate20World) :=
  .step [Gate20World.a, Gate20World.b, Gate20World.c]
    [Gate20World.b, Gate20World.c]
    (.step _ [Gate20World.c]
      (.step _ [] (.nil _)))

/-- The local cardinality bound is sharp: all three available units of scope
budget can be consumed by three strict restrictions. -/
theorem gate20_local_bound_is_sharp :
    gate20SharpDescent.strictShrinkCount = 3 ∧
      gate20SharpDescent.finalScope.length = 0 ∧
      gate20SharpDescent.finalScope.length +
          gate20SharpDescent.strictShrinkCount = 3 := by
  decide +kernel

/-- The concrete Gate-19 `T -> N -> T` recovery trace performs two strict
local cumulative scope restrictions.  This is an observed alignment in the
witness, not a general equivalence between scope shrinkage and recovery
change. -/
theorem gate20_gate19_trace_scope_profile :
    (FiniteConditionalizationTrace.evidenceScopeDescent
      gate19LossReturnTrace () Gate19World.a).strictShrinkCount = 2 ∧
    (FiniteConditionalizationTrace.evidenceScopeDescent
      gate19LossReturnTrace () Gate19World.a).finalScope = [.a] := by
  decide +kernel

end PEL4
