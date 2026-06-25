import PEL4.ActionModel
import PEL4.Belief

namespace PEL4

-- A helper to compute Cartesian product of lists
def listProduct {A B : Type} (la : List A) (lb : List B) : List (A × B) :=
  la.flatMap (fun a => lb.map (fun b => (a, b)))

/-- The Cartesian product of worlds and actions, filtered by 4-valued precondition positivity.
    We delete any (w, a) pair where the evaluation of pre(a) in w is strictly false or gappy.
    This means if pre(a) evaluates to T or B, the world survives. -/
def filterProductWorlds {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : FiniteSet (W × Act) :=
  let all_pairs := listProduct m.worlds a.events
  all_pairs.filter (fun ⟨w, act⟩ => (eval m w (a.pre act)).pos)

/-- The new accessibility relation R' i (w, a) -/
def product_R {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) 
  (i : Ag) (pair : W × Act) : FiniteSet (W × Act) :=
  let ⟨w, act⟩ := pair
  -- The product requires both the original world to be accessible and the action to be indistinguishable.
  let target_w := m.R i w
  let target_a := a.sim i act
  let accessible_pairs := listProduct target_w target_a
  -- Only those that survive the precondition check
  accessible_pairs.filter (fun ⟨w', act'⟩ => (eval m w' (a.pre act')).pos)

/-- A placeholder for the Bayesian probability update function.
    In a full Mathlib implementation, this would sum over `product_R` and normalize.
    For this framework, we define its signature and axiomatically constrain it. -/
def product_mu {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) 
  (i : Ag) (pair : W × Act) (S : FiniteSet (W × Act)) : Rat :=
  -- Dummy implementation. 
  -- Real math: Sum(w',a' in S) [ m.mu i w {w'} * a.plausibility i a' ] / Normalization
  if S.isEmpty then 0 else 1 -- Placeholder

axiom product_mu_total {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) :
  ∀ (i : Ag) (pair : W × Act), product_mu m a i pair (product_R m a i pair) = 1

axiom product_mu_empty {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) :
  ∀ (i : Ag) (pair : W × Act), product_mu m a i pair [] = 0

/-- The 4-PEL Product Update model constructor. -/
def productUpdateModel {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act] [DecidableEq Atom]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) : Model (W × Act) Ag Atom :=
  {
    worlds := filterProductWorlds m a
    R := product_R m a
    mu := product_mu m a
    val := fun ⟨w, _⟩ p => m.val w p -- valuation remains identical to original world
    c := m.c
    mu_total := product_mu_total m a
    mu_empty := product_mu_empty m a
    c_gt_half := m.c_gt_half
    c_le_one := m.c_le_one
  }

end PEL4
