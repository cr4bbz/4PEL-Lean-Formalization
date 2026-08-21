import Lean.Elab.Tactic.Omega
import PEL4.FDE
import PEL4.Theorems

namespace PEL4.Paradoxes

/-!
# Sorites threshold geometry and the gap-glut slack

This module isolates a one-dimensional signed-evidence geometry on a 0--100
scale.  It does not identify vagueness with probability as a philosophical
thesis.  Rather, it asks what four-valued state is induced when positive and
negative support are thresholded independently.

For exclusive evidence we set

  positive support = x,
  negative support = 100 - x.

At threshold c > 50 the middle band is gappy:

  100 - c < x < c.

Its algebraic width is

  c - (100 - c) = 2c - 100.

The same quantity already occurs in the generic 4-PEL glut-boundary theorem as
the minimum overlap mass required for both positive and negative support to
reach threshold.  Thus `2c - 100` has a dual interpretation: gap width under
exclusive evidence, and compulsory glut overlap under sufficiently overlapping
evidence.
-/

/-- Four-valued thresholding of signed evidence on the scaled integer model. -/
def thresholdState100 (c pos neg : Int) : FDEValue :=
  { pos := decide (c ≤ pos)
  , neg := decide (c ≤ neg) }

/-- Exclusive signed evidence: positive and negative masses sum to 100. -/
def exclusiveSoritesValue (c x : Int) : FDEValue :=
  thresholdState100 c x (100 - x)

/-- Exact characterization of the gappy borderline band. -/
theorem exclusive_sorites_gap_iff (c x : Int) :
    exclusiveSoritesValue c x = FDEValue.N ↔
      100 - c < x ∧ x < c := by
  by_cases hp : c ≤ x
  · have hx : ¬ x < c := by omega
    simp [exclusiveSoritesValue, thresholdState100, hp, hx, FDEValue.N]
  · have hx : x < c := by omega
    by_cases hn : c ≤ 100 - x
    · have hlow : ¬ 100 - c < x := by omega
      simp [exclusiveSoritesValue, thresholdState100, hp, hn, hx, hlow,
        FDEValue.N]
    · have hlow : 100 - c < x := by omega
      simp [exclusiveSoritesValue, thresholdState100, hp, hn, hx, hlow,
        FDEValue.N]

/-- Above the majority threshold, exclusive evidence can never be glutty. -/
theorem exclusive_sorites_ne_glut
    (c x : Int)
    (hc : 50 < c) :
    exclusiveSoritesValue c x ≠ FDEValue.B := by
  by_cases hp : c ≤ x
  · have hn : ¬ c ≤ 100 - x := by omega
    simp [exclusiveSoritesValue, thresholdState100, hp, hn, FDEValue.B]
  · simp [exclusiveSoritesValue, thresholdState100, hp, FDEValue.B]

/-- Algebraic width of the exclusive-evidence gap band. -/
def soritesGapWidth100 (c : Int) : Int := 2 * c - 100

/-- The distance between the two threshold boundaries is exactly the familiar
`2c - 100` slack. -/
theorem sorites_gap_band_width (c : Int) :
    c - (100 - c) = soritesGapWidth100 c := by
  simp [soritesGapWidth100]
  omega

/-- Majority thresholds create a strictly positive borderline width. -/
theorem sorites_gap_width_positive
    (c : Int)
    (hc : 50 < c) :
    0 < soritesGapWidth100 c := by
  simp [soritesGapWidth100]
  omega

/-- The generic glut-boundary theorem is controlled by the very same threshold
slack that measures the exclusive-evidence gap width. -/
theorem glut_mass_at_least_sorites_gap_width
    (c : Int)
    (P_T P_B P_N P_F P_pos P_neg : Int)
    (prob_sum : P_T + P_B + P_N + P_F = 100)
    (P_pos_def : P_pos = P_T + P_B)
    (P_neg_def : P_neg = P_F + P_B)
    (belief_pos : P_pos ≥ c)
    (belief_neg : P_neg ≥ c)
    (non_neg_N : P_N ≥ 0) :
    P_B ≥ soritesGapWidth100 c := by
  have h := glut_boundary_theorem c P_T P_B P_N P_F P_pos P_neg
    prob_sum P_pos_def P_neg_def belief_pos belief_neg non_neg_N
  simpa [soritesGapWidth100] using h

/-- Concrete 75% threshold sanity checks. -/
example : exclusiveSoritesValue 75 10 = FDEValue.F := by native_decide
example : exclusiveSoritesValue 75 50 = FDEValue.N := by native_decide
example : exclusiveSoritesValue 75 90 = FDEValue.T := by native_decide
example : soritesGapWidth100 75 = 50 := by native_decide

/-!
## Interpretation

For c > 50, exclusive evidence yields a three-zone line

  F | N | T,

with an N-band of scaled width `2c - 100`.  By contrast, when positive and
negative evidence overlap enough for both sides to meet threshold, the existing
glut-boundary theorem forces at least `2c - 100` units of B-mass.

The same threshold slack therefore governs two opposite forms of epistemic
indeterminacy:

* insufficient joint support produces a gap;
* excessive overlap produces a glut.

This is the formal core of the proposed Gap--Glut Threshold Duality.
-/

end PEL4.Paradoxes
