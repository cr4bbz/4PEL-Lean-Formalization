import PEL4.Dynamics

namespace PEL4.Paradoxes

/-!
# Surprise Examination as dynamic threshold transport

This module isolates a dynamic mechanism at the heart of the Surprise
Examination paradox without pretending to formalize every knowledge-theoretic
assumption of the classical puzzle.

There are three possible exam days, Monday, Wednesday, and Friday.  Initially
they are equiprobable and the Lockean threshold is 2/3.  We then condition on
successive truthful pieces of evidence:

  E1 : the exam is not on Monday,
  E2 : the exam is not on Wednesday.

The atomic proposition "exam on Friday" undergoes the belief trajectory

  F -> N -> T,

while its negation undergoes

  T -> N -> F.

Thus additional information need not preserve a categorical belief status.
The intermediate gap is a genuine threshold phase created by conditioning.
This is the dynamic transport phenomenon we want to distinguish from simple
forgetting.
-/

inductive SurpriseAtom where
  | mon | wed | fri
deriving DecidableEq, Repr

inductive SurpriseAgent where
  | student
deriving DecidableEq, Repr

inductive SurpriseWorld where
  | mon | wed | fri
deriving DecidableEq, Repr

/-- Exactly one exam day is true at each world. -/
def surpriseVal : SurpriseWorld → SurpriseAtom → FDEValue
| SurpriseWorld.mon, SurpriseAtom.mon => FDEValue.T
| SurpriseWorld.mon, SurpriseAtom.wed => FDEValue.F
| SurpriseWorld.mon, SurpriseAtom.fri => FDEValue.F
| SurpriseWorld.wed, SurpriseAtom.mon => FDEValue.F
| SurpriseWorld.wed, SurpriseAtom.wed => FDEValue.T
| SurpriseWorld.wed, SurpriseAtom.fri => FDEValue.F
| SurpriseWorld.fri, SurpriseAtom.mon => FDEValue.F
| SurpriseWorld.fri, SurpriseAtom.wed => FDEValue.F
| SurpriseWorld.fri, SurpriseAtom.fri => FDEValue.T

/-- Uniform prior over the three possible exam days. -/
def surpriseMu : FiniteSet SurpriseWorld → Rat
| S =>
  let pm := if S.contains SurpriseWorld.mon then (1 : Rat) / 3 else 0
  let pw := if S.contains SurpriseWorld.wed then (1 : Rat) / 3 else 0
  let pf := if S.contains SurpriseWorld.fri then (1 : Rat) / 3 else 0
  pm + pw + pf

axiom surprise_mu_total : ∀ (_ : SurpriseAgent) (_ : SurpriseWorld),
  surpriseMu [SurpriseWorld.mon, SurpriseWorld.wed, SurpriseWorld.fri] = 1
axiom surprise_mu_empty : ∀ (_ : SurpriseAgent) (_ : SurpriseWorld),
  surpriseMu [] = 0
axiom surprise_c_gt_half : ∀ (_ : SurpriseAgent), (2 : Rat) / 3 > 1 / 2
axiom surprise_c_le_one : ∀ (_ : SurpriseAgent), (2 : Rat) / 3 ≤ 1

/-- Initial three-day model. -/
def SurpriseModel0 : Model SurpriseWorld SurpriseAgent SurpriseAtom :=
  { worlds := [SurpriseWorld.mon, SurpriseWorld.wed, SurpriseWorld.fri]
  , R := fun _ _ => [SurpriseWorld.mon, SurpriseWorld.wed, SurpriseWorld.fri]
  , mu := fun _ _ => surpriseMu
  , val := surpriseVal
  , c := fun _ => 2 / 3
  , mu_total := surprise_mu_total
  , mu_empty := surprise_mu_empty
  , c_gt_half := surprise_c_gt_half
  , c_le_one := surprise_c_le_one
  }

def examMon : Formula SurpriseAtom SurpriseAgent := Formula.prop SurpriseAtom.mon
def examWed : Formula SurpriseAtom SurpriseAgent := Formula.prop SurpriseAtom.wed
def examFri : Formula SurpriseAtom SurpriseAgent := Formula.prop SurpriseAtom.fri

def notMon : Formula SurpriseAtom SurpriseAgent := Formula.not examMon
def notWed : Formula SurpriseAtom SurpriseAgent := Formula.not examWed
def notFri : Formula SurpriseAtom SurpriseAgent := Formula.not examFri

/-- Belief formulas for the Friday proposition and its negation. -/
def believeFri : Formula SurpriseAtom SurpriseAgent :=
  Formula.bel SurpriseAgent.student examFri

def believeNotFri : Formula SurpriseAtom SurpriseAgent :=
  Formula.bel SurpriseAgent.student notFri

/-- First update: Monday has passed without an exam. -/
def SurpriseModel1 : Model SurpriseWorld SurpriseAgent SurpriseAtom :=
  conditionalize SurpriseModel0 notMon

/-- Second update: Wednesday has also passed without an exam. -/
def SurpriseModel2 : Model SurpriseWorld SurpriseAgent SurpriseAtom :=
  conditionalize SurpriseModel1 notWed

/-- Meta-level positive prediction status.  This is intentionally not encoded
as internal FDE negation: absence of positive belief and `not B(phi)` are
semantically different notions in a four-valued setting. -/
def positivelyPredicts
    (m : Model SurpriseWorld SurpriseAgent SurpriseAtom)
    (phi : Formula SurpriseAtom SurpriseAgent) : Bool :=
  (eval m SurpriseWorld.fri (Formula.bel SurpriseAgent.student phi)).pos

#eval! eval SurpriseModel0 SurpriseWorld.fri believeFri
#eval! eval SurpriseModel1 SurpriseWorld.fri believeFri
#eval! eval SurpriseModel2 SurpriseWorld.fri believeFri

#eval! eval SurpriseModel0 SurpriseWorld.fri believeNotFri
#eval! eval SurpriseModel1 SurpriseWorld.fri believeNotFri
#eval! eval SurpriseModel2 SurpriseWorld.fri believeNotFri

/-- Initially Friday is negatively determined: probability 1/3 for Friday and
2/3 against it. -/
theorem friday_initially_false_belief :
    eval SurpriseModel0 SurpriseWorld.fri believeFri = FDEValue.F := by
  native_decide

/-- After learning that Monday is excluded, Friday has 1/2 positive and 1/2
negative support, both below the 2/3 threshold. -/
theorem friday_becomes_gap_after_not_monday :
    eval SurpriseModel1 SurpriseWorld.fri believeFri = FDEValue.N := by
  native_decide

/-- Once Monday and Wednesday are excluded, Friday becomes certain. -/
theorem friday_becomes_true_belief_after_two_eliminations :
    eval SurpriseModel2 SurpriseWorld.fri believeFri = FDEValue.T := by
  native_decide

/-- Complete dynamic trajectory for the Friday proposition. -/
theorem friday_dynamic_reversal :
    eval SurpriseModel0 SurpriseWorld.fri believeFri = FDEValue.F ∧
    eval SurpriseModel1 SurpriseWorld.fri believeFri = FDEValue.N ∧
    eval SurpriseModel2 SurpriseWorld.fri believeFri = FDEValue.T := by
  native_decide

/-- The complementary proposition traverses the reverse path. -/
theorem not_friday_dynamic_reversal :
    eval SurpriseModel0 SurpriseWorld.fri believeNotFri = FDEValue.T ∧
    eval SurpriseModel1 SurpriseWorld.fri believeNotFri = FDEValue.N ∧
    eval SurpriseModel2 SurpriseWorld.fri believeNotFri = FDEValue.F := by
  native_decide

/-- Before any elimination, no individual exam day is positively predicted at
the 2/3 threshold. -/
theorem no_day_positively_predicted_initially :
    positivelyPredicts SurpriseModel0 examMon = false ∧
    positivelyPredicts SurpriseModel0 examWed = false ∧
    positivelyPredicts SurpriseModel0 examFri = false := by
  native_decide

/-- After eliminating the two earlier days, Friday is positively predicted. -/
theorem friday_positively_predicted_after_eliminations :
    positivelyPredicts SurpriseModel2 examFri = true := by
  native_decide

/-!
## Interpretation

The model does not yet formalize the full self-referential announcement
"the exam will occur and you will not know beforehand which day".  In
particular, 4-PEL currently has probabilistic belief rather than a separate
factive knowledge operator.

What is formalized is the dynamic pressure point used by the backward
elimination argument: once alternatives are successively removed, a day that
was not positively predictable can become positively predictable.  Moreover,
the route is not simply false-to-true; with a majority threshold it passes
through the gap state:

  F -> N -> T.

The complementary belief follows T -> N -> F.  Thus conditionalization and
categorical threshold status do not commute with a naive persistence principle.
This is the Surprise case of the broader structural-transport research program.
-/

end PEL4.Paradoxes
