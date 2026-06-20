import PEL4.Dynamics

namespace PEL4.Paradoxes

inductive LiarAtom where
  | p : LiarAtom
deriving DecidableEq, Repr

inductive Agent where
  | a : Agent
deriving DecidableEq, Repr

inductive World where
  | wT | wF | wB | wN
deriving DecidableEq, Repr

def prior_mu : FiniteSet World → Rat
| S => 
  let t := if S.contains World.wT then (1:Rat)/4 else 0
  let f := if S.contains World.wF then (1:Rat)/4 else 0
  let b := if S.contains World.wB then (1:Rat)/2 else 0
  let n := if S.contains World.wN then (0:Rat)   else 0
  t + f + b + n

theorem liar_mu_total : ∀ (_ : Agent) (_ : World), prior_mu [World.wT, World.wF, World.wB, World.wN] = 1 := by
  intros
  decide

theorem liar_mu_empty : ∀ (_ : Agent) (_ : World), prior_mu [] = 0 := by
  intros
  decide

end PEL4.Paradoxes
