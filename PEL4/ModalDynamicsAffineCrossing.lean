import Init.Data.Rat.Lemmas
import PEL4.ModalDynamicsThresholdCrossing

namespace PEL4

/-!
# Affine threshold crossing on the rational unit interval

`ModalDynamicsThresholdCrossing` proves the endpoint fact that a changed
Lockean threshold bit is exactly a straddling of the threshold by the before
and after support masses.

This module strengthens that endpoint theorem without adding Mathlib.  Between
rational endpoints `x` and `y` consider the directed affine interpolation

```text
  gamma(t) = x + t * (y - x).
```

If the endpoints straddle a rational threshold `c`, then there is an explicit
rational parameter `t` with

```text
  0 <= t <= 1
```

such that `gamma(t) = c`.

This is stronger than endpoint straddling and gives a genuine unit-interval
crossing witness for the affine path.  It is still not an abstract continuity
or intermediate-value theorem: continuity is not represented as a topological
predicate in the current dependency-free core.
-/

/-- Directed affine interpolation from `x` at `t = 0` to `y` at `t = 1`. -/
def affineRatPath (x y t : Rat) : Rat :=
  x + t * (y - x)

/-- Explicit parameter when the path runs from a below-threshold endpoint to an
on/above-threshold endpoint. -/
def affineForwardThresholdParameter (c x y : Rat) : Rat :=
  (c - x) / (y - x)

/-- Explicit parameter for the opposite orientation, when the path begins on or
above threshold and ends below it. -/
def affineBackwardThresholdParameter (c x y : Rat) : Rat :=
  (x - c) / (x - y)

theorem affineRatPath_zero (x y : Rat) :
    affineRatPath x y 0 = x := by
  unfold affineRatPath
  rw [Rat.zero_mul, Rat.add_zero]

theorem affineRatPath_one (x y : Rat) :
    affineRatPath x y 1 = y := by
  unfold affineRatPath
  rw [Rat.one_mul, Rat.add_comm]
  exact Rat.sub_add_cancel

/-- Forward crossing: `x < c <= y` yields an explicit hit parameter in `[0,1]`. -/
theorem affineRatPath_hits_threshold_forward
    (c x y : Rat)
    (hxc : x < c)
    (hcy : c ≤ y) :
    ∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧ affineRatPath x y t = c := by
  have hxy_le : x ≤ y :=
    Rat.le_trans (Rat.le_of_lt hxc) hcy
  have hnot_yx : ¬ y ≤ x := by
    intro hyx
    have hcx : c ≤ x := Rat.le_trans hcy hyx
    exact ((Rat.lt_iff_le_and_not_ge).1 hxc).2 hcx
  have hxy : x < y :=
    (Rat.lt_iff_le_and_not_ge).2 ⟨hxy_le, hnot_yx⟩
  have hden_pos : 0 < y - x :=
    (Rat.lt_iff_sub_pos x y).1 hxy
  have hden_ne : y - x ≠ 0 := Rat.ne_of_gt hden_pos
  have hnum_pos : 0 < c - x :=
    (Rat.lt_iff_sub_pos x c).1 hxc
  let t := affineForwardThresholdParameter c x y
  have ht_pos : 0 < t := by
    unfold t affineForwardThresholdParameter
    apply (Rat.lt_div_iff hden_pos).2
    simpa using hnum_pos
  have ht_nonneg : 0 ≤ t := Rat.le_of_lt ht_pos
  have hnum_le : c - x ≤ y - x := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
    exact (Rat.add_le_add_right).2 hcy
  have ht_not_gt_one : ¬ (1 : Rat) < t := by
    intro ht
    have hden_lt_num : y - x < c - x := by
      unfold t affineForwardThresholdParameter at ht
      have h := (Rat.lt_div_iff hden_pos).1 ht
      simpa using h
    exact ((Rat.lt_iff_le_and_not_ge).1 hden_lt_num).2 hnum_le
  have ht_le_one : t ≤ 1 :=
    (Rat.not_lt).1 ht_not_gt_one
  have hhit : affineRatPath x y t = c := by
    unfold t affineForwardThresholdParameter affineRatPath
    rw [Rat.div_mul_cancel hden_ne, Rat.add_comm]
    exact Rat.sub_add_cancel
  exact ⟨t, ht_nonneg, ht_le_one, hhit⟩

/-- Backward crossing: `y < c <= x` also yields a hit on the directed path from
`x` to `y`, with an explicit parameter in `[0,1]`. -/
theorem affineRatPath_hits_threshold_backward
    (c x y : Rat)
    (hyc : y < c)
    (hcx : c ≤ x) :
    ∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧ affineRatPath x y t = c := by
  have hyx_le : y ≤ x :=
    Rat.le_trans (Rat.le_of_lt hyc) hcx
  have hnot_xy : ¬ x ≤ y := by
    intro hxy
    have hcy : c ≤ y := Rat.le_trans hcx hxy
    exact ((Rat.lt_iff_le_and_not_ge).1 hyc).2 hcy
  have hyx : y < x :=
    (Rat.lt_iff_le_and_not_ge).2 ⟨hyx_le, hnot_xy⟩
  have hden_pos : 0 < x - y :=
    (Rat.lt_iff_sub_pos y x).1 hyx
  have hden_ne : x - y ≠ 0 := Rat.ne_of_gt hden_pos
  have hnum_nonneg : 0 ≤ x - c :=
    (Rat.le_iff_sub_nonneg c x).1 hcx
  let t := affineBackwardThresholdParameter c x y
  have ht_not_neg : ¬ t < 0 := by
    intro ht
    unfold t affineBackwardThresholdParameter at ht
    have hnum_neg : x - c < 0 := by
      have h := (Rat.div_lt_iff hden_pos).1 ht
      simpa using h
    exact ((Rat.not_lt).2 hnum_nonneg) hnum_neg
  have ht_nonneg : 0 ≤ t :=
    (Rat.not_lt).1 ht_not_neg
  have hyc_le : y ≤ c := Rat.le_of_lt hyc
  have hneg_le : -c ≤ -y := Rat.neg_le_neg hyc_le
  have hnum_le : x - c ≤ x - y := by
    rw [Rat.sub_eq_add_neg, Rat.sub_eq_add_neg]
    exact (Rat.add_le_add_left).2 hneg_le
  have ht_not_gt_one : ¬ (1 : Rat) < t := by
    intro ht
    unfold t affineBackwardThresholdParameter at ht
    have hden_lt_num : x - y < x - c := by
      have h := (Rat.lt_div_iff hden_pos).1 ht
      simpa using h
    exact ((Rat.lt_iff_le_and_not_ge).1 hden_lt_num).2 hnum_le
  have ht_le_one : t ≤ 1 :=
    (Rat.not_lt).1 ht_not_gt_one
  have hhit : affineRatPath x y t = c := by
    unfold t affineBackwardThresholdParameter affineRatPath
    rw [← Rat.neg_sub x y, Rat.mul_neg, Rat.div_mul_cancel hden_ne]
    rw [Rat.neg_sub x c, Rat.add_comm]
    exact Rat.sub_add_cancel
  exact ⟨t, ht_nonneg, ht_le_one, hhit⟩

/-- Endpoint threshold straddling therefore forces a literal threshold hit on
the directed rational affine segment between those endpoints. -/
theorem thresholdStraddles_has_affine_unit_crossing
    (c x y : Rat)
    (hStraddle : ThresholdStraddles c x y) :
    ∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧ affineRatPath x y t = c := by
  rcases hStraddle with h | h
  · have hyc : y < c := (Rat.not_le).1 h.2
    exact affineRatPath_hits_threshold_backward c x y hyc h.1
  · have hxc : x < c := (Rat.not_le).1 h.2
    exact affineRatPath_hits_threshold_forward c x y hxc h.1

/-- Positive support straddling under conditionalization has an affine
unit-interval threshold-crossing witness. -/
theorem conditionalized_positive_straddle_has_affine_crossing
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hPos : ConditionalizedPositiveStraddles m E hAdm i w phi) :
    ∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧
      affineRatPath
        (modalPositiveBeliefMass m i w phi)
        (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
        t = m.c i := by
  apply thresholdStraddles_has_affine_unit_crossing
  exact hPos

/-- Negative support analogue. -/
theorem conditionalized_negative_straddle_has_affine_crossing
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hNeg : ConditionalizedNegativeStraddles m E hAdm i w phi) :
    ∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧
      affineRatPath
        (modalNegativeBeliefMass m i w phi)
        (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
        t = m.c i := by
  apply thresholdStraddles_has_affine_unit_crossing
  exact hNeg

/-- Every genuine categorical belief change therefore has a literal affine
threshold hit on at least one of its two support coordinates. -/
theorem conditionalization_belief_change_has_affine_threshold_crossing
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hChange :
      evalModal (conditionalize m E hAdm) w (ModalFormula.bel i phi) ≠
        evalModal m w (ModalFormula.bel i phi)) :
    (∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧
      affineRatPath
        (modalPositiveBeliefMass m i w phi)
        (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
        t = m.c i) ∨
    (∃ t : Rat,
      0 ≤ t ∧ t ≤ 1 ∧
      affineRatPath
        (modalNegativeBeliefMass m i w phi)
        (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
        t = m.c i) := by
  rcases conditionalization_belief_change_implies_support_straddle
      m E hAdm i w phi hChange with hPos | hNeg
  · exact Or.inl
      (conditionalized_positive_straddle_has_affine_crossing
        m E hAdm i w phi hPos)
  · exact Or.inr
      (conditionalized_negative_straddle_has_affine_crossing
        m E hAdm i w phi hNeg)

/-- A two-wall belief transition forces affine threshold hits on both support
coordinates, possibly at different parameters. -/
theorem conditionalization_belief_two_walls_has_two_affine_crossings
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : ModalFormula Atom Ag)
    (hTwo :
      thresholdWallCount
        (evalModal m w (ModalFormula.bel i phi))
        (evalModal (conditionalize m E hAdm) w (ModalFormula.bel i phi)) = 2) :
    (∃ tp : Rat,
      0 ≤ tp ∧ tp ≤ 1 ∧
      affineRatPath
        (modalPositiveBeliefMass m i w phi)
        (modalPositiveBeliefMass (conditionalize m E hAdm) i w phi)
        tp = m.c i) ∧
    (∃ tn : Rat,
      0 ≤ tn ∧ tn ≤ 1 ∧
      affineRatPath
        (modalNegativeBeliefMass m i w phi)
        (modalNegativeBeliefMass (conditionalize m E hAdm) i w phi)
        tn = m.c i) := by
  have hBoth :=
    (conditionalization_belief_two_walls_iff_both_supports_straddle
      m E hAdm i w phi).1 hTwo
  exact ⟨
    conditionalized_positive_straddle_has_affine_crossing
      m E hAdm i w phi hBoth.1,
    conditionalized_negative_straddle_has_affine_crossing
      m E hAdm i w phi hBoth.2
  ⟩

/-!
## Interpretation

The dynamic threshold picture now has a dependency-free affine path layer:

```text
support endpoints straddle c
        ->
explicit rational t in [0,1]
        ->
affine support path hits c exactly.
```

Consequently every categorical belief change under admissible
conditionalization has a literal threshold hit on at least one affine support
coordinate, and every two-wall transition has hits on both coordinates.

This still stops short of a general intermediate-value theorem.  The theorem is
constructive for the affine interpolation chosen here; it does not quantify over
arbitrary continuous support paths.

Working name: **Affine Threshold Crossing**.
-/

end PEL4
