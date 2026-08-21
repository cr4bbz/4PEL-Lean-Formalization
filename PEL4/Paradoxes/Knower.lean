import PEL4.Syntax

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

Classically, T and F fail to stabilize.  In the four-valued space, however,
both the glut B and the gap N are fixed points.  This module makes that
bifurcation explicit inside the actual 4-PEL evaluator.
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

/-!
## Interpretation

The paradox does not force a unique collapse.  Four-valued semantics exposes
a bifurcation between two stable responses to epistemic self-reference:

* B: overdetermination -- both positive and negative epistemic support;
* N: underdetermination -- neither positive nor negative epistemic support.

The distinction also highlights a semantic caution for later Fitch work:
internal FDE negation `not B(phi)` is not automatically the same notion as the
meta-level absence of positive belief in `phi`.
-/

end PEL4.Paradoxes
