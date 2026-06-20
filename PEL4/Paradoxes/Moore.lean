import PEL4.Model
import PEL4.Belief
import PEL4.Syntax

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

-- Let's give w1 probability 1/2 and w2 probability 1/2.
-- So the agent is uncertain about p.
def moore_mu : FiniteSet M_World → Rat
| S => 
  let p1 := if S.contains M_World.w1 then (1:Rat)/2 else 0
  let p2 := if S.contains M_World.w2 then (1:Rat)/2 else 0
  p1 + p2

axiom moore_mu_total : ∀ (_ : M_Agent) (_ : M_World), moore_mu [M_World.w1, M_World.w2] = 1
axiom moore_mu_empty : ∀ (_ : M_Agent) (_ : M_World), moore_mu [] = 0
-- threshold c = 2/3
axiom moore_c_gt_half : ∀ (_ : M_Agent), (2:Rat)/3 > 1/2
axiom moore_c_le_one : ∀ (_ : M_Agent), (2:Rat)/3 ≤ 1

def MooreModel : Model M_World M_Agent MooreAtom :=
  { worlds := [M_World.w1, M_World.w2]
  , R := fun _ _ => [M_World.w1, M_World.w2]
  , mu := fun _ _ => moore_mu
  , val := moore_val
  , c := fun _ => 2/3
  , mu_total := moore_mu_total
  , mu_empty := moore_mu_empty
  , c_gt_half := moore_c_gt_half
  , c_le_one := moore_c_le_one
  }

def p := Formula.prop MooreAtom.p (Ag := M_Agent)
def B_p := Formula.bel M_Agent.a p
def not_B_p := Formula.not B_p

-- Moore's sentence: M ≡ p ∧ ¬B_a(p)
def M := Formula.and p not_B_p

-- What is the value of M at w1?
-- p is T.
-- B_p: mass of p is 1/2 < 2/3. So B_p is F (actually, N if both masses are < c, but F if we define it normally? 
-- Wait, in 4-PEL, if positive mass < c and negative mass < c, the belief is N.
-- Let's see: positive mass of p is 1/2. Negative mass of p is 1/2. 
-- Both < 2/3. So B_p is N.
-- If B_p is N, ¬B_p is N.
-- Then M = T ∧ N = N.
#eval! eval MooreModel M_World.w1 M

-- What is the value of B_a(M) at w1?
def B_M := Formula.bel M_Agent.a M
#eval! eval MooreModel M_World.w1 B_M

end PEL4.Paradoxes
