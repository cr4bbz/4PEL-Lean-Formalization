import PEL4.Model
import PEL4.Belief

namespace PEL4

/-- 
  The Glut Boundary Theorem (Theorem 5.1).
  Since core Lean 4 without Mathlib lacks `linarith` for Rationals,
  we prove this purely algebraically over Integers (representing scaled probabilities, e.g., permille).
  If an agent strictly believes a contradiction (an epistemic glut),
  then the objective probability of the ontological glut (P_B) must be greater than or equal to 2c - 1.
-/
theorem glut_boundary_theorem 
  (c : Int)
  (P_T P_B P_N P_F P_pos P_neg : Int)
  (prob_sum : P_T + P_B + P_N + P_F = 100) -- using 100% as the whole
  (P_pos_def : P_pos = P_T + P_B)
  (P_neg_def : P_neg = P_F + P_B)
  (belief_pos : P_pos ≥ c)
  (belief_neg : P_neg ≥ c)
  (non_neg_N : P_N ≥ 0)
  : P_B ≥ 2 * c - 100 := 
by
  -- P_pos + P_neg = P_T + 2*P_B + P_F
  -- Also, from prob_sum, P_T + P_B + P_F = 100 - P_N
  -- Since P_N ≥ 0, P_T + P_B + P_F ≤ 100
  -- P_pos + P_neg = (P_T + P_B + P_F) + P_B ≤ 100 + P_B
  -- Since P_pos ≥ c and P_neg ≥ c, P_pos + P_neg ≥ 2c
  -- Therefore, 2c ≤ 100 + P_B, meaning P_B ≥ 2c - 100.
  omega

end PEL4
