import PEL4.Model
import PEL4.Belief
import PEL4.Syntax

namespace PEL4.Paradoxes

inductive LotteryAtom where
  | t1 | t2 | t3
deriving DecidableEq, Repr

inductive L_Agent where
  | a
deriving DecidableEq, Repr

inductive L_World where
  | w1 | w2 | w3
deriving DecidableEq, Repr

/-- In world 1, ticket 1 wins (T), others lose (F). And so on. -/
def lottery_val : L_World → LotteryAtom → FDEValue
| L_World.w1, LotteryAtom.t1 => FDEValue.T
| L_World.w1, LotteryAtom.t2 => FDEValue.F
| L_World.w1, LotteryAtom.t3 => FDEValue.F
| L_World.w2, LotteryAtom.t1 => FDEValue.F
| L_World.w2, LotteryAtom.t2 => FDEValue.T
| L_World.w2, LotteryAtom.t3 => FDEValue.F
| L_World.w3, LotteryAtom.t1 => FDEValue.F
| L_World.w3, LotteryAtom.t2 => FDEValue.F
| L_World.w3, LotteryAtom.t3 => FDEValue.T

/-- Equal probability of 1/3 for each world. -/
def lottery_mu : FiniteSet L_World → Rat
| S => 
  let p1 := if S.contains L_World.w1 then (1:Rat)/3 else 0
  let p2 := if S.contains L_World.w2 then (1:Rat)/3 else 0
  let p3 := if S.contains L_World.w3 then (1:Rat)/3 else 0
  p1 + p2 + p3

axiom lottery_mu_total : ∀ (_ : L_Agent) (_ : L_World), lottery_mu [L_World.w1, L_World.w2, L_World.w3] = 1
axiom lottery_mu_empty : ∀ (_ : L_Agent) (_ : L_World), lottery_mu [] = 0
axiom lottery_c_gt_half : ∀ (_ : L_Agent), (2:Rat)/3 > 1/2
axiom lottery_c_le_one : ∀ (_ : L_Agent), (2:Rat)/3 ≤ 1

/-- The Lottery Kripke Model with c = 2/3 -/
def LotteryModel : Model L_World L_Agent LotteryAtom :=
  { worlds := [L_World.w1, L_World.w2, L_World.w3]
  , R := fun _ _ => [L_World.w1, L_World.w2, L_World.w3]
  , mu := fun _ _ => lottery_mu
  , val := lottery_val
  , c := fun _ => 2/3
  , mu_total := lottery_mu_total
  , mu_empty := lottery_mu_empty
  , c_gt_half := lottery_c_gt_half
  , c_le_one := lottery_c_le_one
  }

-- Formulas for "ticket i loses"
def lose_t1 := Formula.not (Formula.prop LotteryAtom.t1 (Ag := L_Agent))
def lose_t2 := Formula.not (Formula.prop LotteryAtom.t2 (Ag := L_Agent))
def lose_t3 := Formula.not (Formula.prop LotteryAtom.t3 (Ag := L_Agent))

-- Belief that ticket i loses
def b_lose_t1 := Formula.bel L_Agent.a lose_t1
def b_lose_t2 := Formula.bel L_Agent.a lose_t2
def b_lose_t3 := Formula.bel L_Agent.a lose_t3

-- Belief that ALL tickets lose
def all_lose := Formula.and lose_t1 (Formula.and lose_t2 lose_t3)
def b_all_lose := Formula.bel L_Agent.a all_lose

-- We evaluate these beliefs at world w1
-- 1. Belief that ticket 1 loses:
-- t1 loses in w2 and w3. Probability = 2/3. Threshold c = 2/3. So Agent believes it (T).
#eval! eval LotteryModel L_World.w1 b_lose_t1

-- 2. Belief that ticket 2 loses:
-- t2 loses in w1 and w3. Probability = 2/3. Agent believes it (T).
#eval! eval LotteryModel L_World.w1 b_lose_t2

-- 3. Belief that ticket 3 loses:
-- t3 loses in w1 and w2. Probability = 2/3. Agent believes it (T).
#eval! eval LotteryModel L_World.w1 b_lose_t3

-- 4. Belief that ALL tickets lose:
-- The conjunction "t1 loses AND t2 loses AND t3 loses" is False in every world.
-- Probability = 0. Agent does NOT believe it (F or N).
-- Since positive mass is 0 (< 2/3) and negative mass is 1 (>= 2/3), it evaluates to F.
-- Wait, the expected state for aggregation paradox is Gap (N) for the *conjunction of beliefs* or the *belief of conjunction*.
-- Actually, the conjunction itself is False everywhere, so B(all_lose) is F.
#eval! eval LotteryModel L_World.w1 b_all_lose

-- Wait! Is the aggregation paradox about the conjunction of beliefs vs the belief of conjunction?
-- Classic Lottery Paradox: Agent believes ~t1, believes ~t2, believes ~t3.
-- So B(~t1) & B(~t2) & B(~t3) evaluates to T & T & T = T.
-- But B(~t1 & ~t2 & ~t3) evaluates to F.
-- Therefore, the agent's beliefs are not closed under conjunction.
-- To represent this in our 4-PEL logic, we can evaluate the meta-formula:
-- (B(~t1) & B(~t2) & B(~t3)) -> B(~t1 & ~t2 & ~t3)
def paradox_implication := 
  Formula.implies (Formula.and b_lose_t1 (Formula.and b_lose_t2 b_lose_t3)) b_all_lose

-- Let's evaluate this implication: T -> F
-- In FDE, T -> F evaluates to F.
#eval! eval LotteryModel L_World.w1 paradox_implication

end PEL4.Paradoxes
