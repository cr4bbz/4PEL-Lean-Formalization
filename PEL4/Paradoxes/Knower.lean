import PEL4.Syntax
import PEL4.EpistemicStatus

namespace PEL4.Paradoxes

/-!
# The Knower paradox as a four-valued epistemic fixed-point problem

The classical Knower sentence is schematically

  K := "K is not known".

In a strict one-world model with threshold 1, the threshold-belief operator
acts transparently on the four FDE values: the unique accessible world carries
all probability mass, so positive and negative support are preserved exactly.
The self-referential right-hand side therefore induces the map

  v |-> not B(v).

Classically, T and F fail to stabilize. In the four-valued space, however,
both the glut B and the gap N are fixed points. This module makes that
bifurcation explicit inside the actual 4-PEL evaluator.

The epistemic-status layer also lets us distinguish this internal FDE negation
from the meta-level absence of positive belief. Those notions agree exactly on
the classical values and diverge on the two nonclassical fixed points.
-/

inductive KnowerAtom where
  | k
deriving DecidableEq, Repr

inductive KnowerAgent where
  | a
deriving DecidableEq, Repr

inductive KnowerWorld where
  | w
deriving DecidableEq, Repr

/-- The unique world has probability one. -/
def knowerMu : FiniteSet KnowerWorld → Rat
| S => if S.contains KnowerWorld.w then 1 else 0

/-- A one-world strict-threshold model whose atomic Knower value is supplied
as a parameter. -/
def KnowerModel (v : FDEValue) : Model KnowerWorld KnowerAgent KnowerAtom :=
  { worlds := [KnowerWorld.w]
  , R := fun _ _ => [KnowerWorld.w]
  , mu := fun _ _ => knowerMu
  , val := fun _ _ => v
  , c := fun _ => 1
  , mu_total := by
      intro _ _
      native_decide
  , mu_empty := by
      intro _ _
      native_decide
  , c_gt_half := by
      intro _
      native_decide
  , c_le_one := by
      intro _
      native_decide
  }

/-- Atomic Knower sentence. -/
def knowerAtomFormula : Formula KnowerAtom KnowerAgent :=
  Formula.prop KnowerAtom.k

/-- The epistemic status attributed to the Knower sentence. -/
def knowerBelief : Formula KnowerAtom KnowerAgent :=
  Formula.bel KnowerAgent.a knowerAtomFormula

/-- Self-referential right-hand side: "the Knower sentence is not believed".
Here `not` is the internal FDE negation of the belief state. -/
def knowerRhs : Formula KnowerAtom KnowerAgent :=
  Formula.not knowerBelief

/-- One step of the Knower fixed-point equation, evaluated by the full 4-PEL
semantics rather than by a hand-written truth table. -/
def knowerStep (v : FDEValue) : FDEValue :=
  eval (KnowerModel v) KnowerWorld.w knowerRhs

/-- Meta-level signal that positive threshold belief in the Knower atom is
absent. This is intentionally distinct from internal `not B(k)`. -/
def knowerLacksPositiveBelief (v : FDEValue) : Bool :=
  lacksPositiveBelief (KnowerModel v) KnowerAgent.a KnowerWorld.w knowerAtomFormula

#eval! knowerStep FDEValue.T
#eval! knowerStep FDEValue.F
#eval! knowerStep FDEValue.B
#eval! knowerStep FDEValue.N

/-- Classical truth oscillates to falsity. -/
theorem knower_true_steps_to_false :
    knowerStep FDEValue.T = FDEValue.F := by
  native_decide

/-- Classical falsity oscillates to truth. -/
theorem knower_false_steps_to_true :
    knowerStep FDEValue.F = FDEValue.T := by
  native_decide

/-- Glutty self-reference is stable. -/
theorem knower_glut_fixed :
    knowerStep FDEValue.B = FDEValue.B := by
  native_decide

/-- Gappy self-reference is stable as well. -/
theorem knower_gap_fixed :
    knowerStep FDEValue.N = FDEValue.N := by
  native_decide

/-- Complete four-valued fixed-point classification.

The Knower map has exactly the two nonclassical fixed points B and N; T and F
form a two-cycle. -/
theorem knower_fixed_iff_glut_or_gap (v : FDEValue) :
    knowerStep v = v ↔ v = FDEValue.B ∨ v = FDEValue.N := by
  rcases v with ⟨pos, neg⟩
  cases pos <;> cases neg <;> native_decide

/-- Internal Knower negation and meta-level absence of positive belief agree
exactly on the classical subspace. -/
theorem knower_internal_negation_matches_absence_iff_classical
    (v : FDEValue) :
    (knowerStep v).pos = knowerLacksPositiveBelief v ↔
      isClassical v = true := by
  rcases v with ⟨pos, neg⟩
  cases pos <;> cases neg <;> native_decide

/-- At the glut fixed point, internal negation remains positively supported,
while positive belief is not absent. -/
theorem knower_glut_internal_not_differs_from_absence :
    (knowerStep FDEValue.B).pos = true ∧
    knowerLacksPositiveBelief FDEValue.B = false := by
  native_decide

/-- At the gap fixed point, internal negation lacks positive support, while
positive belief is absent. -/
theorem knower_gap_internal_not_differs_from_absence :
    (knowerStep FDEValue.N).pos = false ∧
    knowerLacksPositiveBelief FDEValue.N = true := by
  native_decide

/-!
## Interpretation

The paradox does not force a unique collapse. Four-valued semantics exposes
a bifurcation between two stable responses to epistemic self-reference:

* B: overdetermination -- both positive and negative epistemic support;
* N: underdetermination -- neither positive nor negative epistemic support.

The status layer sharpens the interpretation. The equation implemented here is
an internal-negation equation, not an absence-of-belief equation. Those readings
coincide in classical states but split exactly at B and N. Therefore a later
formalization of the natural-language Knower should make explicit which notion
of "not known" or "not believed" it intends to represent.
-/

end PEL4.Paradoxes
