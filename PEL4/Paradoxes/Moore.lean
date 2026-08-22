import PEL4.Model
import PEL4.Belief
import PEL4.Syntax
import PEL4.EpistemicStatus

namespace PEL4.Paradoxes

inductive MooreAtom where
  | p
deriving DecidableEq, Repr

inductive M_Agent where
  | a
deriving DecidableEq, Repr

inductive M_World where
  | w1 | w2
deriving DecidableEq, Repr

-- In w1: p is True
-- In w2: p is False
def moore_val : M_World → MooreAtom → FDEValue
| M_World.w1, MooreAtom.p => FDEValue.T
| M_World.w2, MooreAtom.p => FDEValue.F

-- Give w1 probability 1/2 and w2 probability 1/2.
-- The agent is therefore below the 2/3 threshold on both sides of p.
def moore_mu : FiniteSet M_World → Rat
| S =>
  let p1 := if S.contains M_World.w1 then (1 : Rat) / 2 else 0
  let p2 := if S.contains M_World.w2 then (1 : Rat) / 2 else 0
  p1 + p2

theorem moore_mu_total : ∀ (_ : M_Agent) (_ : M_World),
    moore_mu [M_World.w1, M_World.w2] = 1 := by
  intro _ _
  native_decide

theorem moore_mu_empty : ∀ (_ : M_Agent) (_ : M_World), moore_mu [] = 0 := by
  intro _ _
  native_decide

theorem moore_c_gt_half : ∀ (_ : M_Agent), (2 : Rat) / 3 > 1 / 2 := by
  intro _
  native_decide

theorem moore_c_le_one : ∀ (_ : M_Agent), (2 : Rat) / 3 ≤ 1 := by
  intro _
  native_decide

def MooreModel : Model M_World M_Agent MooreAtom :=
  { worlds := [M_World.w1, M_World.w2]
  , R := fun _ _ => [M_World.w1, M_World.w2]
  , mu := fun _ _ => moore_mu
  , val := moore_val
  , c := fun _ => 2 / 3
  , mu_total := moore_mu_total
  , mu_empty := moore_mu_empty
  , c_gt_half := moore_c_gt_half
  , c_le_one := moore_c_le_one
  }

def p := Formula.prop MooreAtom.p (Ag := M_Agent)
def B_p := Formula.bel M_Agent.a p
def not_B_p := Formula.not B_p

/-- Object-language Moore sentence using internal FDE negation. -/
def M := Formula.and p not_B_p

/-- Meta-level Moore condition: p has positive truth support at the actual world,
while positive threshold belief in p is absent.  This is deliberately not
identified with the object-language formula `p and not B(p)`. -/
def mooreMetaCondition : Bool :=
  (eval MooreModel M_World.w1 p).pos &&
    lacksPositiveBelief MooreModel M_Agent.a M_World.w1 p

#eval! eval MooreModel M_World.w1 M

def B_M := Formula.bel M_Agent.a M
#eval! eval MooreModel M_World.w1 B_M

/-- The threshold belief state for p is a gap: both 1/2 masses lie below 2/3. -/
theorem moore_belief_is_gap :
    eval MooreModel M_World.w1 B_p = FDEValue.N := by
  native_decide

/-- Positive belief in p is absent in the meta-level status sense. -/
theorem moore_lacks_positive_belief :
    lacksPositiveBelief MooreModel M_Agent.a M_World.w1 p = true := by
  native_decide

/-- Negative belief is absent as well; the belief state is underdetermined,
not strict disbelief. -/
theorem moore_lacks_negative_belief :
    lacksNegativeBelief MooreModel M_Agent.a M_World.w1 p = true := by
  native_decide

/-- Internal negation preserves the gap rather than turning it into a positive
claim that belief is absent. -/
theorem moore_internal_negated_belief_is_gap :
    eval MooreModel M_World.w1 not_B_p = FDEValue.N := by
  native_decide

/-- The crucial Moore separation: internal `not B(p)` has no positive support,
while the meta-level statement that positive belief is absent is true. -/
theorem moore_internal_not_differs_from_belief_absence :
    (eval MooreModel M_World.w1 not_B_p).pos = false ∧
    lacksPositiveBelief MooreModel M_Agent.a M_World.w1 p = true := by
  native_decide

/-- The ordinary-language status reading "p is true here but I lack positive
belief in p" is satisfied even though the object-language FDE conjunction
`p and not B(p)` evaluates to a gap. -/
theorem moore_meta_condition_holds :
    mooreMetaCondition = true := by
  native_decide

/-- The object-language Moore sentence itself remains gappy. -/
theorem moore_object_language_sentence_is_gap :
    eval MooreModel M_World.w1 M = FDEValue.N := by
  native_decide

end PEL4.Paradoxes
