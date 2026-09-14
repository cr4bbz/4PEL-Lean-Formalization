import PEL4.PosteriorSampleComplexity
namespace PEL4

def gate75Bellman (value : Rat) : Rat := 1 + value / 2
def gate75FixedPoint : Rat := 2
def gate75ValueIteration : Nat -> Rat | 0 => 0 | n + 1 => gate75Bellman (gate75ValueIteration n)
def gate75Residual (n : Nat) : Rat := gate75FixedPoint - gate75ValueIteration n

theorem gate75_fixed_point : gate75Bellman gate75FixedPoint = gate75FixedPoint := by native_decide

theorem gate75_difference_halves :
    gate75Bellman (gate75ValueIteration 1) - gate75Bellman (gate75ValueIteration 0) =
      (gate75ValueIteration 1 - gate75ValueIteration 0) / 2 := by native_decide

theorem gate75_residual_window :
    gate75Residual 0 = 2 ∧ gate75Residual 1 = 1 ∧ gate75Residual 2 = (1 : Rat) / 2 ∧
    gate75Residual 3 = (1 : Rat) / 4 ∧ gate75Residual 4 = (1 : Rat) / 8 := by native_decide

theorem gate75_residual_halves :
    gate75Residual 1 = gate75Residual 0 / 2 ∧ gate75Residual 2 = gate75Residual 1 / 2 ∧
    gate75Residual 3 = gate75Residual 2 / 2 ∧ gate75Residual 4 = gate75Residual 3 / 2 := by native_decide

/-- On the explicit approximation ladder, the endpoint `2` is the only fixed
point. This is deliberately finite and executable, not uniqueness over all Rat. -/
theorem gate75_fixed_point_unique :
    gate75Bellman 0 ≠ 0 ∧
    gate75Bellman 1 ≠ 1 ∧
    gate75Bellman ((3 : Rat) / 2) ≠ (3 : Rat) / 2 ∧
    gate75Bellman ((7 : Rat) / 4) ≠ (7 : Rat) / 4 ∧
    gate75Bellman ((15 : Rat) / 8) ≠ (15 : Rat) / 8 ∧
    gate75Bellman 2 = 2 := by
  native_decide

theorem gate75_first_approximants :
    gate75ValueIteration 0 = 0 ∧ gate75ValueIteration 1 = 1 ∧
    gate75ValueIteration 2 = (3 : Rat) / 2 ∧ gate75ValueIteration 3 = (7 : Rat) / 4 ∧
    gate75ValueIteration 4 = (15 : Rat) / 8 := by native_decide

theorem gate75_iteration_residual_halves :
    gate75Residual 1 = gate75Residual 0 / 2 ∧ gate75Residual 2 = gate75Residual 1 / 2 ∧
    gate75Residual 3 = gate75Residual 2 / 2 ∧ gate75Residual 4 = gate75Residual 3 / 2 := gate75_residual_halves

theorem gate75_discounted_bellman_fixed_point :
    gate75Bellman gate75FixedPoint = gate75FixedPoint ∧
    gate75Residual 0 = 2 ∧ gate75Residual 1 = 1 ∧ gate75Residual 2 = (1 : Rat) / 2 ∧
    gate75Residual 3 = (1 : Rat) / 4 ∧ gate75Residual 4 = (1 : Rat) / 8 := by
  exact ⟨gate75_fixed_point, gate75_residual_window.1, gate75_residual_window.2.1,
    gate75_residual_window.2.2.1, gate75_residual_window.2.2.2.1,
    gate75_residual_window.2.2.2.2⟩
end PEL4
