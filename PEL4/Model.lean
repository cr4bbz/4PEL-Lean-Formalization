import PEL4.FDE

namespace PEL4

/-- A simple representation of finite sets as Lists without duplicates.
    For this prototype, we just use List and ensure no duplicates externally. -/
def FiniteSet (α : Type) := List α

/-- Probability measure represented using Rational numbers. 
    It evaluates the probability of a subset of worlds. -/
def ProbMeasure (W : Type) := FiniteSet W → Rat

/-- The 4-PEL Finite Kripke Model. -/
structure Model (W Ag Atom : Type) [DecidableEq W] where
  /-- The set of all worlds in the model -/
  worlds : FiniteSet W
  /-- The accessibility relation $R_i(w)$ -/
  R : Ag → W → FiniteSet W
  /-- The local probability measure $\mu_{i,w}$ -/
  mu : Ag → W → ProbMeasure W
  /-- The valuation function assigning 4-values to atomic propositions at worlds -/
  val : W → Atom → FDEValue
  /-- The global Lockean threshold for belief for each agent -/
  c : Ag → Rat
  
  /-- Axiom: Total probability of the accessible worlds is 1. -/
  mu_total : ∀ (i : Ag) (w : W), mu i w (R i w) = 1
  /-- Axiom: Probability of empty set is 0. -/
  mu_empty : ∀ (i : Ag) (w : W), mu i w [] = 0
  /-- Axiom: Lockean threshold is strictly greater than 1/2. -/
  c_gt_half : ∀ i, c i > 1/2
  /-- Axiom: Lockean threshold is at most 1. -/
  c_le_one : ∀ i, c i ≤ 1

end PEL4
