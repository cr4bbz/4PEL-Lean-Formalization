import Lean.Elab.Tactic.Omega

namespace PEL4.Paradoxes

/-!
# Generic fixed-marginal fiber dimension count

For `n` claims there are `2^n - 1` nonempty exact conflict patterns.
Fixing the carrier mass contributes one affine equation and fixing all `n`
local glut marginals contributes `n` further affine equations.

For `n >= 2` these `n + 1` equations are independent.  Hence the generic
affine solution space has

  (2^n - 1) - (n + 1) = 2^n - n - 2

degrees of freedom.

This file keeps the argument elementary and dependency-free.  It formalizes
both the combinatorial coordinate count and an independence certificate for
the carrier-plus-marginal constraints.  It deliberately does not identify a
Mathlib `finrank`, because this project currently has no Mathlib dependency.
The dimension statement should therefore be read as the exact affine parameter
count justified by those two formal ingredients.

Intersecting the affine solution space with the nonnegative incidence simplex
may lower the local dimension at boundary/degenerate profiles.  The count here
is the generic/interior dimension.
-/

/-- Dependency-free representation of `2^n`. -/
def powTwo : Nat → Nat
| 0 => 1
| n + 1 => 2 * powTwo n

/-- Enumerate all Boolean incidence patterns of arity `n`. -/
def allBoolPatterns : Nat → List (List Bool)
| 0 => [[]]
| n + 1 =>
    (allBoolPatterns n).map (fun p => false :: p) ++
      (allBoolPatterns n).map (fun p => true :: p)

/-- There are exactly `2^n` Boolean patterns of arity `n`. -/
theorem allBoolPatterns_length :
    ∀ n : Nat, (allBoolPatterns n).length = powTwo n
| 0 => rfl
| n + 1 => by
    simp [allBoolPatterns, powTwo, allBoolPatterns_length n]
    omega

/-- Enumerate exactly the nonempty Boolean patterns recursively.

At arity `n+1`, every `true`-prefixed pattern is nonempty, while a
`false`-prefixed pattern is nonempty exactly when its tail already was. -/
def allNonemptyBoolPatterns : Nat → List (List Bool)
| 0 => []
| n + 1 =>
    (allBoolPatterns n).map (fun p => true :: p) ++
      (allNonemptyBoolPatterns n).map (fun p => false :: p)

/-- Powers of two are always positive. -/
theorem powTwo_pos : ∀ n : Nat, 0 < powTwo n
| 0 => by simp [powTwo]
| n + 1 => by
    have ih := powTwo_pos n
    simp [powTwo]
    omega

/-- The exact conflict-incidence simplex has `2^n - 1` nonempty coordinates. -/
theorem allNonemptyBoolPatterns_length :
    ∀ n : Nat, (allNonemptyBoolPatterns n).length = powTwo n - 1
| 0 => by simp [allNonemptyBoolPatterns, powTwo]
| n + 1 => by
    have hall := allBoolPatterns_length n
    have ih := allNonemptyBoolPatterns_length n
    have hp := powTwo_pos n
    simp [allNonemptyBoolPatterns, powTwo, hall, ih]
    omega

/-!
## Independence certificate for carrier + marginal constraints

Consider a possible linear dependence among the `n+1` affine constraint rows.
Let `a0` be the coefficient of the carrier row and let the remaining
coefficients multiply the `n` marginal rows.

Evaluation on a singleton conflict pattern `{i}` gives

  a0 + ai = 0.

For `n >= 2`, evaluation on one pair pattern `{1,2}` also gives

  a0 + a1 + a2 = 0.

The singleton equations imply `a1 = a2 = -a0`; substituting into the pair
equation forces `a0 = 0`, and then every `ai = 0`.

`ConstraintTestRelation` packages exactly this finite independence witness.
-/

/-- A candidate linear relation that vanishes on every singleton test and on
one pair test.  For two or more marginal coefficients these tests are already
sufficient to force the relation to be trivial. -/
def ConstraintTestRelation (a0 : Int) : List Int → Prop
| c1 :: c2 :: rest =>
    (∀ c, c ∈ c1 :: c2 :: rest → a0 + c = 0) ∧
      a0 + c1 + c2 = 0
| _ => True

/-- Carrier and marginal rows are independent once at least two claims exist.

This is the concrete row-independence certificate: any relation vanishing on
all singleton incidence columns and one pair column has all coefficients zero.
-/
theorem carrier_marginal_constraint_independence
    (a0 c1 c2 : Int)
    (rest : List Int)
    (h : ConstraintTestRelation a0 (c1 :: c2 :: rest)) :
    a0 = 0 ∧
      ∀ c, c ∈ c1 :: c2 :: rest → c = 0 := by
  rcases h with ⟨hsingle, hpair⟩
  have h1 : a0 + c1 = 0 := hsingle c1 (by simp)
  have h2 : a0 + c2 = 0 := hsingle c2 (by simp)
  have ha0 : a0 = 0 := by omega
  constructor
  · exact ha0
  · intro c hc
    have hsingleC : a0 + c = 0 := hsingle c hc
    omega

/-- Number of carrier-plus-marginal affine equations.  The theorem above
certifies that all `n+1` are independent for `n >= 2`; at arity one the carrier
and sole marginal equation coincide. -/
def fixedMarginalConstraintCount (n : Nat) : Nat := n + 1

/-- Raw affine parameter count obtained by subtracting the carrier-plus-marginal
equation count from the nonempty incidence-coordinate count.  Its geometric
interpretation as the generic fiber dimension is justified for `n >= 2` by the
independence certificate above. -/
def fixedMarginalFiberFreedom (n : Nat) : Nat :=
  (powTwo n - 1) - fixedMarginalConstraintCount n

/-- Exact arithmetic parameter-count formula:

  (2^n - 1) - (n + 1) = 2^n - n - 2.

Here `powTwo n` is the dependency-free definition of `2^n` above. -/
theorem fixedMarginalFiberFreedom_formula (n : Nat) :
    fixedMarginalFiberFreedom n = powTwo n - n - 2 := by
  simp [fixedMarginalFiberFreedom, fixedMarginalConstraintCount]
  omega

/-- For `n >= 2`, the independent-constraint certificate promotes the raw
parameter count to the generic affine fixed-marginal fiber dimension count. -/
theorem generic_fixedMarginalFiber_dimension_count
    (n : Nat) (_hn : 2 ≤ n) :
    fixedMarginalFiberFreedom n = powTwo n - n - 2 :=
  fixedMarginalFiberFreedom_formula n

/-- Sanity checks matching the already-formalized three-claim tetrahedral
fiber and the first higher-arity cases. -/
example : fixedMarginalFiberFreedom 2 = 0 := by decide
example : fixedMarginalFiberFreedom 3 = 3 := by decide
example : fixedMarginalFiberFreedom 4 = 10 := by decide
example : fixedMarginalFiberFreedom 5 = 25 := by decide

/-!
## Philosophical reading

The visible first-order description grows only linearly with arity (`n`
marginals plus one carrier coordinate), while the exact conflict incidence
structure grows exponentially (`2^n - 1` coordinates).  Their difference
therefore grows as `2^n - n - 2` for the generic `n >= 2` fiber.

This quantifies the hidden-interaction reservoir behind marginal
underdetermination: as the number of jointly considered claims increases,
first-order epistemic summaries discard an exponentially growing family of
higher-order conflict degrees of freedom.
-/

end PEL4.Paradoxes
