import PEL4.Model

namespace PEL4

/-- Helper to filter a finite set based on a predicate. -/
def filterWorlds {W : Type} (worlds : FiniteSet W) (p : W → Bool) : FiniteSet W :=
  worlds.filter p

/-- The threshold belief operator.
    Evaluates whether the local probability of the positive and negative extensions
    meet the Lockean threshold `c`. -/
def belief {W Ag : Type} [DecidableEq W] (m : Model W Ag) (i : Ag) (w : W) (phi : Prop) (c : Rat) : FDEValue :=
  let R_w := m.R i w
  
  -- The subset of accessible worlds where phi is positively supported
  let pos_worlds := filterWorlds R_w (fun w' => (m.val w' phi).pos)
  -- The subset of accessible worlds where phi is negatively supported
  let neg_worlds := filterWorlds R_w (fun w' => (m.val w' phi).neg)
  
  -- The probability mass of those subsets
  let prob_pos := m.mu i w pos_worlds
  let prob_neg := m.mu i w neg_worlds
  
  -- Return the 4-value evaluated against the threshold
  { pos := prob_pos ≥ c, neg := prob_neg ≥ c }

end PEL4
