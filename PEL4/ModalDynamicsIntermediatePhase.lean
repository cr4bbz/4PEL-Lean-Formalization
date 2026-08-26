import PEL4.ModalDynamicsCrossingOrder

namespace PEL4

/-!
# Intermediate FDE phases between sequential affine threshold crossings

Affine Crossing-Order Geometry gives two unique threshold-hit times for every
two-wall support transition.  This module asks what four-valued phase appears
between those two times when the hits are not simultaneous.

For positive-first motion (`tp < tn`) we use the rational midpoint

```text
  tm = (tp + tn) / 2.
```

The target theorem says that at `tm` the positive coordinate has already moved
to its target threshold side, while the negative coordinate is still on its
source threshold side.  Negative-first motion is symmetric.

This turns temporal crossing order into an intermediate vertex of the Boolean
threshold square.

Important semantic boundary: the path here is the explicitly constructed
affine interpolation of the two support masses.  An intermediate support point
is not yet claimed to arise from an actual intermediate admissible model update.
-/

/-- FDE status obtained by thresholding a pair of rational support masses. -/
def supportThresholdState (c p n : Rat) : FDEValue :=
  { pos := decide (c ≤ p)
  , neg := decide (c ≤ n) }

/-- FDE status along the two-coordinate affine support interpolation. -/
def affineThresholdState
    (c p0 p1 n0 n1 t : Rat) : FDEValue :=
  supportThresholdState c
    (affineRatPath p0 p1 t)
    (affineRatPath n0 n1 t)

/-- If the positive threshold wall is crossed first, the intermediate Boolean
vertex takes the positive coordinate from the target and the negative coordinate
from the source. -/
def positiveFirstIntermediate (source target : FDEValue) : FDEValue :=
  { pos := target.pos
  , neg := source.neg }

/-- Negative-first analogue. -/
def negativeFirstIntermediate (source target : FDEValue) : FDEValue :=
  { pos := source.pos
  , neg := target.neg }

/-- Midpoint of two rational parameters. -/
def ratMidpoint (a b : Rat) : Rat :=
  (a + b) / 2

/-- Multiplication by rational two is repeated addition. -/
theorem rat_mul_two (a : Rat) :
    a * 2 = a + a := by
  calc
    a * 2 = a * (1 + 1) := by
      congr 1
      decide
    _ = a * 1 + a * 1 := Rat.mul_add _ _ _
    _ = a + a := by simp only [Rat.mul_one]

/-- The rational midpoint of two strictly ordered parameters lies strictly
between them. -/
theorem ratMidpoint_strictly_between
    (a b : Rat)
    (hab : a < b) :
    a < ratMidpoint a b ∧ ratMidpoint a b < b := by
  have htwo : (0 : Rat) < 2 := by decide
  constructor
  · unfold ratMidpoint
    apply (Rat.lt_div_iff htwo).2
    rw [rat_mul_two]
    exact (Rat.add_lt_add_left).2 hab
  · unfold ratMidpoint
    apply (Rat.div_lt_iff htwo).2
    rw [rat_mul_two]
    exact (Rat.add_lt_add_right).2 hab

/-- Affine interpolation is strictly increasing in its parameter when the
endpoint masses are strictly increasing. -/
theorem affineRatPath_strictMono_of_endpoints_lt
    (x y t s : Rat)
    (hxy : x < y)
    (hts : t < s) :
    affineRatPath x y t < affineRatPath x y s := by
  have hden : 0 < y - x :=
    (Rat.lt_iff_sub_pos x y).1 hxy
  unfold affineRatPath
  exact (Rat.add_lt_add_left).2
    ((Rat.mul_lt_mul_right hden).2 hts)

/-- Affine interpolation is strictly decreasing in its parameter when the
endpoint masses are strictly decreasing. -/
theorem affineRatPath_strictAnti_of_endpoints_gt
    (x y t s : Rat)
    (hyx : y < x)
    (hts : t < s) :
    affineRatPath x y s < affineRatPath x y t := by
  have hden : 0 < x - y :=
    (Rat.lt_iff_sub_pos y x).1 hyx
  have hmul : t * (x - y) < s * (x - y) :=
    (Rat.mul_lt_mul_right hden).2 hts
  have hneg : -(s * (x - y)) < -(t * (x - y)) :=
    Rat.neg_lt_neg hmul
  have hrewrite (u : Rat) :
      u * (y - x) = -(u * (x - y)) := by
    rw [← Rat.neg_sub x y, Rat.mul_neg]
  unfold affineRatPath
  rw [hrewrite s, hrewrite t]
  exact (Rat.add_lt_add_left).2 hneg

/-- Upward threshold straddling forces increasing endpoints. -/
theorem thresholdStraddles_up_endpoints_lt
    (c x y : Rat)
    (hUp : c ≤ y ∧ ¬ c ≤ x) :
    x < y := by
  have hxc : x < c := (Rat.not_le).1 hUp.2
  have hxy_le : x ≤ y :=
    Rat.le_trans (Rat.le_of_lt hxc) hUp.1
  have hnot_yx : ¬ y ≤ x := by
    intro hyx
    exact hUp.2 (Rat.le_trans hUp.1 hyx)
  exact (Rat.lt_iff_le_and_not_ge).2 ⟨hxy_le, hnot_yx⟩

/-- Downward threshold straddling forces decreasing endpoints. -/
theorem thresholdStraddles_down_endpoints_lt
    (c x y : Rat)
    (hDown : c ≤ x ∧ ¬ c ≤ y) :
    y < x := by
  have hyc : y < c := (Rat.not_le).1 hDown.2
  have hyx_le : y ≤ x :=
    Rat.le_trans (Rat.le_of_lt hyc) hDown.1
  have hnot_xy : ¬ x ≤ y := by
    intro hxy
    exact hDown.2 (Rat.le_trans hDown.1 hxy)
  exact (Rat.lt_iff_le_and_not_ge).2 ⟨hyx_le, hnot_xy⟩

/-- Before the unique crossing time, an affine straddling path has the same
threshold bit as its source endpoint. -/
theorem affine_threshold_side_before_crossing_eq_source
    (c x y tc t : Rat)
    (hStraddle : ThresholdStraddles c x y)
    (hHit : affineRatPath x y tc = c)
    (ht : t < tc) :
    decide (c ≤ affineRatPath x y t) = decide (c ≤ x) := by
  rcases hStraddle with hDown | hUp
  · have hyx := thresholdStraddles_down_endpoints_lt c x y hDown
    have hlt : c < affineRatPath x y t := by
      have h := affineRatPath_strictAnti_of_endpoints_gt
        x y t tc hyx ht
      rw [hHit] at h
      exact h
    have hle : c ≤ affineRatPath x y t := Rat.le_of_lt hlt
    simp [hDown.1, hle]
  · have hxy := thresholdStraddles_up_endpoints_lt c x y hUp
    have hlt : affineRatPath x y t < c := by
      have h := affineRatPath_strictMono_of_endpoints_lt
        x y t tc hxy ht
      rw [hHit] at h
      exact h
    have hnot : ¬ c ≤ affineRatPath x y t := (Rat.not_le).2 hlt
    simp [hUp.2, hnot]

/-- After the unique crossing time, an affine straddling path has the same
threshold bit as its target endpoint. -/
theorem affine_threshold_side_after_crossing_eq_target
    (c x y tc t : Rat)
    (hStraddle : ThresholdStraddles c x y)
    (hHit : affineRatPath x y tc = c)
    (ht : tc < t) :
    decide (c ≤ affineRatPath x y t) = decide (c ≤ y) := by
  rcases hStraddle with hDown | hUp
  · have hyx := thresholdStraddles_down_endpoints_lt c x y hDown
    have hlt : affineRatPath x y t < c := by
      have h := affineRatPath_strictAnti_of_endpoints_gt
        x y tc t hyx ht
      rw [hHit] at h
      exact h
    have hnot : ¬ c ≤ affineRatPath x y t := (Rat.not_le).2 hlt
    simp [hDown.2, hnot]
  · have hxy := thresholdStraddles_up_endpoints_lt c x y hUp
    have hlt : c < affineRatPath x y t := by
      have h := affineRatPath_strictMono_of_endpoints_lt
        x y tc t hxy ht
      rw [hHit] at h
      exact h
    have hle : c ≤ affineRatPath x y t := Rat.le_of_lt hlt
    simp [hUp.1, hle]

/-- Midpoint between a positive-first pair of crossings. -/
def affineCrossingMidpoint
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1) : Rat :=
  ratMidpoint pair.tp pair.tn

/-- Positive-first order places the crossing midpoint strictly after the
positive hit and strictly before the negative hit. -/
theorem affineCrossingMidpoint_between_positive_first
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1)
    (hOrder : pair.tp < pair.tn) :
    pair.tp < affineCrossingMidpoint pair ∧
      affineCrossingMidpoint pair < pair.tn := by
  unfold affineCrossingMidpoint
  exact ratMidpoint_strictly_between pair.tp pair.tn hOrder

/-- Negative-first order gives the symmetric strict interval. -/
theorem affineCrossingMidpoint_between_negative_first
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1)
    (hOrder : pair.tn < pair.tp) :
    pair.tn < affineCrossingMidpoint pair ∧
      affineCrossingMidpoint pair < pair.tp := by
  unfold affineCrossingMidpoint
  simpa [ratMidpoint, Rat.add_comm] using
    (ratMidpoint_strictly_between pair.tn pair.tp hOrder)

/-- Positive-first temporal order determines the complete FDE status at the
crossing midpoint: positive has reached the target side while negative remains
on the source side. -/
theorem affineCrossingPair_positive_first_midpoint_state
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1)
    (hPos : ThresholdStraddles c p0 p1)
    (hNeg : ThresholdStraddles c n0 n1)
    (hOrder : pair.tp < pair.tn) :
    affineThresholdState c p0 p1 n0 n1
        (affineCrossingMidpoint pair) =
      positiveFirstIntermediate
        (supportThresholdState c p0 n0)
        (supportThresholdState c p1 n1) := by
  have hBetween :=
    affineCrossingMidpoint_between_positive_first pair hOrder
  have hp := affine_threshold_side_after_crossing_eq_target
    c p0 p1 pair.tp (affineCrossingMidpoint pair)
    hPos pair.positive_hit hBetween.1
  have hn := affine_threshold_side_before_crossing_eq_source
    c n0 n1 pair.tn (affineCrossingMidpoint pair)
    hNeg pair.negative_hit hBetween.2
  unfold affineThresholdState supportThresholdState positiveFirstIntermediate
  exact (fdeValue_mk_eq_iff _ _ _ _).2 ⟨hp, hn⟩

/-- Negative-first temporal order determines the symmetric intermediate state. -/
theorem affineCrossingPair_negative_first_midpoint_state
    {c p0 p1 n0 n1 : Rat}
    (pair : AffineThresholdCrossingPair c p0 p1 n0 n1)
    (hPos : ThresholdStraddles c p0 p1)
    (hNeg : ThresholdStraddles c n0 n1)
    (hOrder : pair.tn < pair.tp) :
    affineThresholdState c p0 p1 n0 n1
        (affineCrossingMidpoint pair) =
      negativeFirstIntermediate
        (supportThresholdState c p0 n0)
        (supportThresholdState c p1 n1) := by
  have hBetween :=
    affineCrossingMidpoint_between_negative_first pair hOrder
  have hp := affine_threshold_side_before_crossing_eq_source
    c p0 p1 pair.tp (affineCrossingMidpoint pair)
    hPos pair.positive_hit hBetween.2
  have hn := affine_threshold_side_after_crossing_eq_target
    c n0 n1 pair.tn (affineCrossingMidpoint pair)
    hNeg pair.negative_hit hBetween.1
  unfold affineThresholdState supportThresholdState negativeFirstIntermediate
  exact (fdeValue_mk_eq_iff _ _ _ _).2 ⟨hp, hn⟩

/-- For opposite endpoint vertices, the positive-first intermediate is adjacent
to both source and target. -/
theorem positiveFirstIntermediate_adjacent_to_diagonal_endpoints
    (source target : FDEValue)
    (hOpp : thresholdWallCount source target = 2) :
    thresholdWallCount source
        (positiveFirstIntermediate source target) = 1 ∧
      thresholdWallCount
        (positiveFirstIntermediate source target) target = 1 := by
  have hDiff := (thresholdWallCount_eq_two_iff source target).1 hOpp
  constructor
  · simp [thresholdWallCount, positiveFirstIntermediate, hDiff.1]
  · simp [thresholdWallCount, positiveFirstIntermediate, hDiff.2]

/-- Negative-first intermediate is likewise adjacent to both diagonal endpoints. -/
theorem negativeFirstIntermediate_adjacent_to_diagonal_endpoints
    (source target : FDEValue)
    (hOpp : thresholdWallCount source target = 2) :
    thresholdWallCount source
        (negativeFirstIntermediate source target) = 1 ∧
      thresholdWallCount
        (negativeFirstIntermediate source target) target = 1 := by
  have hDiff := (thresholdWallCount_eq_two_iff source target).1 hOpp
  constructor
  · simp [thresholdWallCount, negativeFirstIntermediate, hDiff.2]
  · simp [thresholdWallCount, negativeFirstIntermediate, hDiff.1]

/-- Complete concrete table for the two diagonal orientations and their reverses. -/
theorem affine_diagonal_intermediate_vertex_table :
    positiveFirstIntermediate FDEValue.N FDEValue.B = FDEValue.T ∧
    negativeFirstIntermediate FDEValue.N FDEValue.B = FDEValue.F ∧
    positiveFirstIntermediate FDEValue.B FDEValue.N = FDEValue.F ∧
    negativeFirstIntermediate FDEValue.B FDEValue.N = FDEValue.T ∧
    positiveFirstIntermediate FDEValue.T FDEValue.F = FDEValue.N ∧
    negativeFirstIntermediate FDEValue.T FDEValue.F = FDEValue.B ∧
    positiveFirstIntermediate FDEValue.F FDEValue.T = FDEValue.B ∧
    negativeFirstIntermediate FDEValue.F FDEValue.T = FDEValue.N := by
  native_decide

/-- Every two-wall conditionalized belief transition therefore admits an affine
crossing pair whose temporal order either is simultaneous or determines an
actual adjacent intermediate FDE phase at the rational crossing midpoint. -/
theorem conditionalization_belief_two_walls_intermediate_phase
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hTwo :
      thresholdWallCount
        (evalModal m w (ModalFormula.bel i phi))
        (evalModal (conditionalize m E hAdm) w (ModalFormula.bel i phi)) = 2) :
    ∃ pair : AffineThresholdCrossingPair
        (m.c i)
        (modalPositiveBeliefMass m i w phi)
        (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
        (modalNegativeBeliefMass m i w phi)
        (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi),
      (pair.tp = pair.tn ∧
        ∃ t : Rat,
          affineRatPath
              (modalPositiveBeliefMass m i w phi)
              (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
              t = m.c i ∧
          affineRatPath
              (modalNegativeBeliefMass m i w phi)
              (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
              t = m.c i) ∨
      (pair.tp < pair.tn ∧
        affineThresholdState
            (m.c i)
            (modalPositiveBeliefMass m i w phi)
            (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
            (modalNegativeBeliefMass m i w phi)
            (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
            (affineCrossingMidpoint pair) =
          positiveFirstIntermediate
            (supportThresholdState
              (m.c i)
              (modalPositiveBeliefMass m i w phi)
              (modalNegativeBeliefMass m i w phi))
            (supportThresholdState
              (m.c i)
              (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
              (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi))) ∨
      (pair.tn < pair.tp ∧
        affineThresholdState
            (m.c i)
            (modalPositiveBeliefMass m i w phi)
            (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
            (modalNegativeBeliefMass m i w phi)
            (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
            (affineCrossingMidpoint pair) =
          negativeFirstIntermediate
            (supportThresholdState
              (m.c i)
              (modalPositiveBeliefMass m i w phi)
              (modalNegativeBeliefMass m i w phi))
            (supportThresholdState
              (m.c i)
              (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
              (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi))) := by
  have hBoth :=
    (conditionalization_belief_two_walls_iff_both_supports_straddle
      m E hAdm i w phi).1 hTwo
  have hPos := hBoth.1
  have hNeg := hBoth.2
  unfold ConditionalizedPositiveStraddles at hPos
  unfold ConditionalizedNegativeStraddles at hNeg
  rcases conditionalization_belief_two_walls_crossing_order
      m E hAdm i w phi hTwo with ⟨pair, hOrder⟩
  refine ⟨pair, ?_⟩
  rcases hOrder with hPosFirst | hSim | hNegFirst
  · exact Or.inr (Or.inl ⟨hPosFirst,
      affineCrossingPair_positive_first_midpoint_state
        pair hPos hNeg hPosFirst⟩)
  · exact Or.inl ⟨hSim,
      (affineCrossingPair_simultaneous_iff_common_hit pair).1 hSim⟩
  · exact Or.inr (Or.inr ⟨hNegFirst,
      affineCrossingPair_negative_first_midpoint_state
        pair hPos hNeg hNegFirst⟩)

/-!
## Interpretation

Sequential diagonal motion in the threshold square cannot jump directly from
one corner to its opposite along the affine support interpolation.  The first
crossed threshold coordinate changes while the second remains on its source
side, so the path occupies the adjacent intermediate vertex.

The verified target table is intended to be:

```text
N -> B : positive first -> T ; negative first -> F
B -> N : positive first -> F ; negative first -> T
T -> F : positive first -> N ; negative first -> B
F -> T : positive first -> B ; negative first -> N
```

Simultaneous crossing is the exceptional case where the support path passes
through `(c,c)` and no open temporal interval separates the two wall events.

Again, this classifies the constructed affine support interpolation, not yet a
sequence of intermediate probabilistic models.

Working name: **Affine Intermediate-Phase Geometry**.
-/

end PEL4
