import PEL4.Dynamics

namespace PEL4.Paradoxes

inductive LiarAtom where
  | p : LiarAtom
deriving DecidableEq, Repr

inductive Agent where
  | a : Agent
deriving DecidableEq, Repr

-- The four worlds represent the four pure epistemic states
inductive World where
  | wT | wF | wB | wN
deriving DecidableEq, Repr

def liar_val : World → LiarAtom → FDEValue
| World.wT, _ => FDEValue.T
| World.wF, _ => FDEValue.F
| World.wB, _ => FDEValue.B
| World.wN, _ => FDEValue.N

-- Prior Probability: P_T = 1/4, P_F = 1/4, P_B = 1/2, P_N = 0
-- This sum to 1 over the four accessible worlds.
def prior_mu : FiniteSet World → Rat
| S => 
  let t := if S.contains World.wT then (1:Rat)/4 else 0
  let f := if S.contains World.wF then (1:Rat)/4 else 0
  let b := if S.contains World.wB then (1:Rat)/2 else 0
  let n := if S.contains World.wN then (0:Rat)   else 0
  t + f + b + n

axiom liar_mu_total : ∀ (_ : Agent) (_ : World), prior_mu [World.wT, World.wF, World.wB, World.wN] = 1
axiom liar_mu_empty : ∀ (_ : Agent) (_ : World), prior_mu [] = 0
axiom liar_c_gt_half : ∀ (_ : Agent), (3:Rat)/4 > 1/2
axiom liar_c_le_one : ∀ (_ : Agent), (3:Rat)/4 ≤ 1

-- The prior Kripke Model
def LiarModel : Model World Agent LiarAtom :=
  { worlds := [World.wT, World.wF, World.wB, World.wN]
  , R := fun _ _ => [World.wT, World.wF, World.wB, World.wN]
  , mu := fun _ _ => prior_mu
  , val := liar_val
  , c := fun _ => 3/4
  , mu_total := liar_mu_total
  , mu_empty := liar_mu_empty
  , c_gt_half := liar_c_gt_half
  , c_le_one := liar_c_le_one
  }

-- The Evidence: E ≡ p ↔ ¬p
-- defined as (p → ¬p) ∧ (¬p → p)
def LiarEvidence : Formula LiarAtom Agent :=
  let p := Formula.prop LiarAtom.p
  let not_p := Formula.not p
  Formula.and (Formula.implies p not_p) (Formula.implies not_p p)

#eval! (conditionalize LiarModel LiarEvidence).mu Agent.a World.wT [World.wB]

end PEL4.Paradoxes
