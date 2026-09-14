import PEL4.PosteriorSampleComplexity

namespace PEL4

/-!
# Gate 75: discounted Bellman fixed point

Gate 69 used a finite horizon. Gate 75 isolates the mathematical core needed for
an infinite-horizon extension in the smallest exact witness: a discounted scalar
Bellman operator with discount `1/2`.

The operator is `T(v) = 1 + v/2`. It has the unique fixed point `2`, differences
are halved by one application, and value iteration from zero inherits the same
exact residual-halving law at every finite stage.
-/

/-- A minimal discounted Bellman operator with immediate reward one and discount
factor one half. -/
def gate75Bellman (value : Rat) : Rat := 1 + value / 2

/-- Candidate infinite-horizon value. -/
def gate75FixedPoint : Rat := 2

/-- The candidate is exactly a fixed point. -/
theorem gate75_fixed_point :
    gate75Bellman gate75FixedPoint = gate75FixedPoint := by
  norm_num [gate75Bellman, gate75FixedPoint]

/-- One Bellman application contracts signed differences by exactly one half. -/
theorem gate75_difference_halves (left right : Rat) :
    gate75Bellman left - gate75Bellman right = (left - right) / 2 := by
  unfold gate75Bellman
  ring

/-- Equivalently, residual error relative to the fixed point is halved. -/
theorem gate75_residual_halves (value : Rat) :
    gate75Bellman value - gate75FixedPoint =
      (value - gate75FixedPoint) / 2 := by
  unfold gate75Bellman gate75FixedPoint
  ring

/-- The fixed point is unique. -/
theorem gate75_fixed_point_unique
    (value : Rat)
    (hFixed : gate75Bellman value = value) :
    value = gate75FixedPoint := by
  unfold gate75Bellman gate75FixedPoint at hFixed ⊢
  linarith

/-- Finite approximants of the infinite-horizon value iteration. -/
def gate75ValueIteration : Nat -> Rat
  | 0 => 0
  | n + 1 => gate75Bellman (gate75ValueIteration n)

/-- Every iteration halves the previous residual, uniformly for all iteration
counts. -/
theorem gate75_iteration_residual_halves (n : Nat) :
    gate75ValueIteration (n + 1) - gate75FixedPoint =
      (gate75ValueIteration n - gate75FixedPoint) / 2 := by
  simpa [gate75ValueIteration] using
    gate75_residual_halves (gate75ValueIteration n)

/-- First exact approximants: `0, 1, 3/2, 7/4, 15/8`. -/
theorem gate75_first_approximants :
    gate75ValueIteration 0 = 0 ∧
    gate75ValueIteration 1 = 1 ∧
    gate75ValueIteration 2 = (3 : Rat) / 2 ∧
    gate75ValueIteration 3 = (7 : Rat) / 4 ∧
    gate75ValueIteration 4 = (15 : Rat) / 8 := by
  native_decide

/-- Main Gate-75 result: the discounted Bellman witness has a unique fixed point
and an exact geometric residual law under value iteration. -/
theorem gate75_discounted_bellman_fixed_point :
    gate75Bellman gate75FixedPoint = gate75FixedPoint ∧
    (∀ value,
      gate75Bellman value = value -> value = gate75FixedPoint) ∧
    (∀ left right,
      gate75Bellman left - gate75Bellman right = (left - right) / 2) ∧
    (∀ n,
      gate75ValueIteration (n + 1) - gate75FixedPoint =
        (gate75ValueIteration n - gate75FixedPoint) / 2) := by
  exact ⟨gate75_fixed_point,
    gate75_fixed_point_unique,
    gate75_difference_halves,
    gate75_iteration_residual_halves⟩

/-!
## Gate-75 boundary

This gate does not yet instantiate a complete infinite-horizon 4PEL belief MDP,
nor does it invoke a topological Banach fixed-point theorem. It machine-checks
the algebraic heart of discounted convergence: unique fixed point and geometric
error contraction. That is the stable foundation needed before lifting the same
pattern to richer belief-state operators.
-/

end PEL4
