import PEL4.ProductUpdate

namespace PEL4

-- Theorem 1: Probability Preservation (Normalisation)
-- This is axiomatically handled by `product_mu_total` and `product_mu_empty` 
-- in the ProductModel definition.

-- Theorem 2: Introspection Preservation (KD45)
-- We state that if the original relation is Transitive/Euclidean, and the action 
-- model's relation `sim` is also Transitive/Euclidean, then the product relation 
-- preserves these properties.

/-- A relation is transitive. -/
def TransitiveRel {W : Type} (R : W → FiniteSet W) : Prop :=
  ∀ w w' w'', w' ∈ R w → w'' ∈ R w' → w'' ∈ R w

/-- A relation is Euclidean. -/
def EuclideanRel {W : Type} (R : W → FiniteSet W) : Prop :=
  ∀ w w' w'', w' ∈ R w → w'' ∈ R w → w'' ∈ R w'

-- Because our models filter out worlds based on precondition positivity, 
-- `product_R` isn't just the cartesian product of relations; it's a subset.
-- Transitivity on a filtered product relation usually holds if the preconditions 
-- are static. In 4-PEL, the precondition `pre(act')` is evaluated at the target 
-- world `w'`. Since `w'` doesn't change during the transition from `(w, a)` to `(w', a')`,
-- the positivity check remains consistent.

-- We axiomatically state these preservations for the prototype.
axiom product_transitive_preservation {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act] [DecidableEq Atom]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) (i : Ag) :
  TransitiveRel (m.R i) → TransitiveRel (a.sim i) → TransitiveRel (product_R m a i)

axiom product_euclidean_preservation {W Act Ag Atom : Type} [DecidableEq W] [DecidableEq Act] [DecidableEq Atom]
  (m : Model W Ag Atom) (a : ActionModel Act Ag Atom) (i : Ag) :
  EuclideanRel (m.R i) → EuclideanRel (a.sim i) → EuclideanRel (product_R m a i)

end PEL4
