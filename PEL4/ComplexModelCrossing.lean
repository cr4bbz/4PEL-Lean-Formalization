import PEL4.ComplexModelPath
import PEL4.ModalDynamicsIntermediatePhase

namespace PEL4

/-!
# Crossing order on affine complex strong-model paths

`ComplexModelPath` packages the two affine support masses of every
probability-free formula as a rational complex coordinate on a complete strong
model path.  This module connects that packaged path to the existing unique
threshold-crossing theory.

The endpoint hypothesis is stated about the actual modal belief values of the
two weight-generated strong endpoint models.  If both threshold bits differ,
the positive and negative components of the complex coordinate each have a
unique unit-interval hit.  Those hits occur at actual intermediate strong
models and have exactly one of the three orders: positive first, simultaneous,
or negative first.
-/

/-- The convex and displacement presentations of a rational affine segment
are extensionally equal. -/
theorem affineRatPath_eq_convexCombination (x y t : Rat) :
    affineRatPath x y t = (1 - t) * x + t * y := by
  simp [affineRatPath, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_neg, Rat.neg_mul,
    Rat.add_comm, Rat.add_left_comm]

/-- Thresholding the two components of the modal support coordinate is exactly
the object-language belief value. -/
theorem evalModal_bel_eq_modalSupportComplexThresholdState
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    evalModal m w (ModalFormula.bel i phi) =
      supportThresholdState (m.c i)
        (modalSupportComplexCoord m i w phi).re
        (modalSupportComplexCoord m i w phi).im := by
  rw [evalModal_bel_eq_threshold_pair]
  rfl

/-- Along a convex strong-model path, the belief value of every
probability-free formula is exactly the threshold state of its affine complex
support coordinate. -/
theorem convexStrongModelAt_evalBel_probabilityFree_eq_affineThresholdState
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    evalModal
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          t ht0 ht1).toModel
        w (ModalFormula.bel i phi) =
      affineThresholdState
        (c i)
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).im
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).im
        t := by
  rw [evalModal_bel_eq_modalSupportComplexThresholdState]
  change supportThresholdState (c i)
      (modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          t ht0 ht1).toModel i w phi).re
      (modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          t ht0 ht1).toModel i w phi).im = _
  rw [convexStrongModelAt_modalSupportComplexCoord_probabilityFree
    worlds R q0 q1 val c h0 h1 hcHalf hcOne
    t ht0 ht1 i w hFree]
  unfold affineThresholdState
  rw [ComplexCoord.affine_re, ComplexCoord.affine_im,
    ← affineRatPath_eq_convexCombination,
    ← affineRatPath_eq_convexCombination]

/-- A two-wall difference between the endpoint belief values is equivalent to
both components of their modal support coordinate straddling the threshold.
This packages the endpoint argument needed by every model-level crossing
classification. -/
theorem strongModelEndpoints_two_walls_supports_straddle
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTwo :
      thresholdWallCount
        (evalModal
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          w (ModalFormula.bel i phi))
        (evalModal
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          w (ModalFormula.bel i phi)) = 2) :
    ThresholdStraddles (c i)
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).re ∧
      ThresholdStraddles (c i)
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).im
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).im := by
  let m0 := weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne
  let m1 := weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne
  let z0 := modalSupportComplexCoord m0 i w phi
  let z1 := modalSupportComplexCoord m1 i w phi
  have hTwoCoord :
      thresholdWallCount
        (supportThresholdState (c i) z0.re z0.im)
        (supportThresholdState (c i) z1.re z1.im) = 2 := by
    change thresholdWallCount
      (evalModal m0 w (ModalFormula.bel i phi))
      (evalModal m1 w (ModalFormula.bel i phi)) = 2 at hTwo
    rw [evalModal_bel_eq_modalSupportComplexThresholdState,
      evalModal_bel_eq_modalSupportComplexThresholdState] at hTwo
    change thresholdWallCount
      (supportThresholdState (c i) z0.re z0.im)
      (supportThresholdState (c i) z1.re z1.im) = 2 at hTwo
    exact hTwo
  have hDiff :=
    (thresholdWallCount_eq_two_iff
      (supportThresholdState (c i) z0.re z0.im)
      (supportThresholdState (c i) z1.re z1.im)).1 hTwoCoord
  have hPos : ThresholdStraddles (c i) z0.re z1.re :=
    (threshold_decision_ne_iff_straddles (c i) z0.re z1.re).1 (by
      simpa [supportThresholdState] using hDiff.1)
  have hNeg : ThresholdStraddles (c i) z0.im z1.im :=
    (threshold_decision_ne_iff_straddles (c i) z0.im z1.im).1 (by
      simpa [supportThresholdState] using hDiff.2)
  exact ⟨hPos, hNeg⟩

/-- A two-wall endpoint transition of a probability-free formula on a convex
strong-model path has two unique model-realized crossing times and an exact
temporal order. -/
theorem convexStrongModelPath_probabilityFree_crossing_order
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi)
    (hTwo :
      thresholdWallCount
        (evalModal
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          w (ModalFormula.bel i phi))
        (evalModal
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          w (ModalFormula.bel i phi)) = 2) :
    ∃ pair : AffineThresholdCrossingPair
        (c i)
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).im
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).im,
      (pair.tp < pair.tn ∨ pair.tp = pair.tn ∨ pair.tn < pair.tp) ∧
      (modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          pair.tp pair.tp_nonneg pair.tp_le_one).toModel
        i w phi).re = c i ∧
      (modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          pair.tn pair.tn_nonneg pair.tn_le_one).toModel
        i w phi).im = c i := by
  let m0 := weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne
  let m1 := weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne
  let z0 := modalSupportComplexCoord m0 i w phi
  let z1 := modalSupportComplexCoord m1 i w phi
  have hTwoCoord :
      thresholdWallCount
        (supportThresholdState (c i) z0.re z0.im)
        (supportThresholdState (c i) z1.re z1.im) = 2 := by
    change thresholdWallCount
      (evalModal m0 w (ModalFormula.bel i phi))
      (evalModal m1 w (ModalFormula.bel i phi)) = 2 at hTwo
    rw [evalModal_bel_eq_modalSupportComplexThresholdState,
      evalModal_bel_eq_modalSupportComplexThresholdState] at hTwo
    change thresholdWallCount
      (supportThresholdState (c i) z0.re z0.im)
      (supportThresholdState (c i) z1.re z1.im) = 2 at hTwo
    exact hTwo
  have hDiff :=
    (thresholdWallCount_eq_two_iff
      (supportThresholdState (c i) z0.re z0.im)
      (supportThresholdState (c i) z1.re z1.im)).1 hTwoCoord
  have hPos : ThresholdStraddles (c i) z0.re z1.re :=
    (threshold_decision_ne_iff_straddles (c i) z0.re z1.re).1 (by
      simpa [supportThresholdState] using hDiff.1)
  have hNeg : ThresholdStraddles (c i) z0.im z1.im :=
    (threshold_decision_ne_iff_straddles (c i) z0.im z1.im).1 (by
      simpa [supportThresholdState] using hDiff.2)
  rcases thresholdStraddles_has_unique_affine_unit_crossing
      (c i) z0.re z1.re hPos with
    ⟨tp, htp0, htp1, hpHit, hpUnique⟩
  rcases thresholdStraddles_has_unique_affine_unit_crossing
      (c i) z0.im z1.im hNeg with
    ⟨tn, htn0, htn1, hnHit, hnUnique⟩
  let pair : AffineThresholdCrossingPair
      (c i) z0.re z1.re z0.im z1.im :=
    { tp := tp
    , tn := tn
    , tp_nonneg := htp0
    , tp_le_one := htp1
    , tn_nonneg := htn0
    , tn_le_one := htn1
    , positive_hit := hpHit
    , negative_hit := hnHit
    , positive_unique := hpUnique
    , negative_unique := hnUnique }
  refine ⟨pair, affineCrossingPair_order_trichotomy pair, ?_, ?_⟩
  · rw [convexStrongModelAt_modalSupportComplexCoord_probabilityFree
      worlds R q0 q1 val c h0 h1 hcHalf hcOne
      pair.tp pair.tp_nonneg pair.tp_le_one i w hFree]
    change (ComplexCoord.affine pair.tp z0 z1).re = c i
    rw [ComplexCoord.affine_re,
      ← affineRatPath_eq_convexCombination z0.re z1.re pair.tp]
    exact pair.positive_hit
  · rw [convexStrongModelAt_modalSupportComplexCoord_probabilityFree
      worlds R q0 q1 val c h0 h1 hcHalf hcOne
      pair.tn pair.tn_nonneg pair.tn_le_one i w hFree]
    change (ComplexCoord.affine pair.tn z0 z1).im = c i
    rw [ComplexCoord.affine_im,
      ← affineRatPath_eq_convexCombination z0.im z1.im pair.tn]
    exact pair.negative_hit

/-- If the positive support wall is crossed first, the rational crossing
midpoint defines an actual complete strong model whose belief value is the
forced positive-first intermediate FDE phase. -/
theorem convexStrongModelPath_probabilityFree_positive_first_midpoint
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi)
    (pair : AffineThresholdCrossingPair
      (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).im
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).im)
    (hPos : ThresholdStraddles (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).re)
    (hNeg : ThresholdStraddles (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).im
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).im)
    (hOrder : pair.tp < pair.tn) :
    ∃ htm0 : 0 ≤ affineCrossingMidpoint pair,
      ∃ htm1 : affineCrossingMidpoint pair ≤ 1,
        evalModal
            (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
              (affineCrossingMidpoint pair) htm0 htm1).toModel
            w (ModalFormula.bel i phi) =
          positiveFirstIntermediate
            (evalModal
              (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
              w (ModalFormula.bel i phi))
            (evalModal
              (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
              w (ModalFormula.bel i phi)) := by
  have hBetween :=
    affineCrossingMidpoint_between_positive_first pair hOrder
  have htm0 : 0 ≤ affineCrossingMidpoint pair :=
    Rat.le_trans pair.tp_nonneg (Rat.le_of_lt hBetween.1)
  have htm1 : affineCrossingMidpoint pair ≤ 1 :=
    Rat.le_trans (Rat.le_of_lt hBetween.2) pair.tn_le_one
  refine ⟨htm0, htm1, ?_⟩
  rw [convexStrongModelAt_evalBel_probabilityFree_eq_affineThresholdState
    worlds R q0 q1 val c h0 h1 hcHalf hcOne
    (affineCrossingMidpoint pair) htm0 htm1 i w hFree]
  rw [evalModal_bel_eq_modalSupportComplexThresholdState,
    evalModal_bel_eq_modalSupportComplexThresholdState]
  change affineThresholdState _ _ _ _ _ (affineCrossingMidpoint pair) =
    positiveFirstIntermediate
      (supportThresholdState (c i) _ _)
      (supportThresholdState (c i) _ _)
  exact affineCrossingPair_positive_first_midpoint_state
    pair hPos hNeg hOrder

/-- If the negative support wall is crossed first, the same model construction
realizes the symmetric forced intermediate FDE phase. -/
theorem convexStrongModelPath_probabilityFree_negative_first_midpoint
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi)
    (pair : AffineThresholdCrossingPair
      (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).im
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).im)
    (hPos : ThresholdStraddles (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).re)
    (hNeg : ThresholdStraddles (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).im
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).im)
    (hOrder : pair.tn < pair.tp) :
    ∃ htm0 : 0 ≤ affineCrossingMidpoint pair,
      ∃ htm1 : affineCrossingMidpoint pair ≤ 1,
        evalModal
            (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
              (affineCrossingMidpoint pair) htm0 htm1).toModel
            w (ModalFormula.bel i phi) =
          negativeFirstIntermediate
            (evalModal
              (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
              w (ModalFormula.bel i phi))
            (evalModal
              (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
              w (ModalFormula.bel i phi)) := by
  have hBetween :=
    affineCrossingMidpoint_between_negative_first pair hOrder
  have htm0 : 0 ≤ affineCrossingMidpoint pair :=
    Rat.le_trans pair.tn_nonneg (Rat.le_of_lt hBetween.1)
  have htm1 : affineCrossingMidpoint pair ≤ 1 :=
    Rat.le_trans (Rat.le_of_lt hBetween.2) pair.tp_le_one
  refine ⟨htm0, htm1, ?_⟩
  rw [convexStrongModelAt_evalBel_probabilityFree_eq_affineThresholdState
    worlds R q0 q1 val c h0 h1 hcHalf hcOne
    (affineCrossingMidpoint pair) htm0 htm1 i w hFree]
  rw [evalModal_bel_eq_modalSupportComplexThresholdState,
    evalModal_bel_eq_modalSupportComplexThresholdState]
  change affineThresholdState _ _ _ _ _ (affineCrossingMidpoint pair) =
    negativeFirstIntermediate
      (supportThresholdState (c i) _ _)
      (supportThresholdState (c i) _ _)
  exact affineCrossingPair_negative_first_midpoint_state
    pair hPos hNeg hOrder

/-- If both support walls are crossed at the same parameter, the common
crossing is realized by a complete strong model at the intersection `(c,c)`.
Because threshold membership is inclusive, the belief value at that single
parameter is the glut value `B`. -/
theorem convexStrongModelPath_probabilityFree_simultaneous_crossing
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi)
    (pair : AffineThresholdCrossingPair
      (c i)
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).re
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne) i w phi).im
      (modalSupportComplexCoord
        (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne) i w phi).im)
    (hSim : pair.tp = pair.tn) :
    evalModal
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          pair.tp pair.tp_nonneg pair.tp_le_one).toModel
        w (ModalFormula.bel i phi) = FDEValue.B ∧
      (modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          pair.tp pair.tp_nonneg pair.tp_le_one).toModel
        i w phi).re = c i ∧
      (modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          pair.tp pair.tp_nonneg pair.tp_le_one).toModel
        i w phi).im = c i := by
  let m0 := weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne
  let m1 := weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne
  let z0 := modalSupportComplexCoord m0 i w phi
  let z1 := modalSupportComplexCoord m1 i w phi
  let mt :=
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      pair.tp pair.tp_nonneg pair.tp_le_one).toModel
  have hz : modalSupportComplexCoord mt i w phi =
      ComplexCoord.affine pair.tp z0 z1 := by
    exact convexStrongModelAt_modalSupportComplexCoord_probabilityFree
      worlds R q0 q1 val c h0 h1 hcHalf hcOne
      pair.tp pair.tp_nonneg pair.tp_le_one i w hFree
  have hre : (modalSupportComplexCoord mt i w phi).re = c i := by
    rw [hz, ComplexCoord.affine_re,
      ← affineRatPath_eq_convexCombination z0.re z1.re pair.tp]
    exact pair.positive_hit
  have him : (modalSupportComplexCoord mt i w phi).im = c i := by
    rw [hz, ComplexCoord.affine_im,
      ← affineRatPath_eq_convexCombination z0.im z1.im pair.tp]
    rw [hSim]
    exact pair.negative_hit
  refine ⟨?_, hre, him⟩
  rw [convexStrongModelAt_evalBel_probabilityFree_eq_affineThresholdState
    worlds R q0 q1 val c h0 h1 hcHalf hcOne
    pair.tp pair.tp_nonneg pair.tp_le_one i w hFree]
  change affineThresholdState (c i)
    z0.re z1.re z0.im z1.im pair.tp = FDEValue.B
  have hneg : affineRatPath z0.im z1.im pair.tp = c i := by
    rw [hSim]
    exact pair.negative_hit
  unfold affineThresholdState
  rw [pair.positive_hit, hneg]
  simp [supportThresholdState, FDEValue.B]

/-- Complete model-theoretic classification of a diagonal belief transition
along a convex path of strong probability models. Exactly one temporal case is
realized: a positive-first adjacent phase, a simultaneous glut at `(c,c)`, or
the symmetric negative-first adjacent phase. -/
theorem convexStrongModelPath_probabilityFree_complete_crossing_classification
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (q0 q1 : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (h0 : ∀ i w, FiniteWeightDistribution (R i w) (q0 i w))
    (h1 : ∀ i w, FiniteWeightDistribution (R i w) (q1 i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi)
    (hTwo :
      thresholdWallCount
        (evalModal
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          w (ModalFormula.bel i phi))
        (evalModal
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          w (ModalFormula.bel i phi)) = 2) :
    ∃ pair : AffineThresholdCrossingPair
        (c i)
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).re
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi).im
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi).im,
      (pair.tp < pair.tn ∧
        ∃ htm0 : 0 ≤ affineCrossingMidpoint pair,
          ∃ htm1 : affineCrossingMidpoint pair ≤ 1,
            evalModal
                (convexStrongModelAt worlds R q0 q1 val c
                  h0 h1 hcHalf hcOne
                  (affineCrossingMidpoint pair) htm0 htm1).toModel
                w (ModalFormula.bel i phi) =
              positiveFirstIntermediate
                (evalModal
                  (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
                  w (ModalFormula.bel i phi))
                (evalModal
                  (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
                  w (ModalFormula.bel i phi))) ∨
      (pair.tp = pair.tn ∧
        evalModal
            (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
              pair.tp pair.tp_nonneg pair.tp_le_one).toModel
            w (ModalFormula.bel i phi) = FDEValue.B ∧
        (modalSupportComplexCoord
          (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
            pair.tp pair.tp_nonneg pair.tp_le_one).toModel
          i w phi).re = c i ∧
        (modalSupportComplexCoord
          (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
            pair.tp pair.tp_nonneg pair.tp_le_one).toModel
          i w phi).im = c i) ∨
      (pair.tn < pair.tp ∧
        ∃ htm0 : 0 ≤ affineCrossingMidpoint pair,
          ∃ htm1 : affineCrossingMidpoint pair ≤ 1,
            evalModal
                (convexStrongModelAt worlds R q0 q1 val c
                  h0 h1 hcHalf hcOne
                  (affineCrossingMidpoint pair) htm0 htm1).toModel
                w (ModalFormula.bel i phi) =
              negativeFirstIntermediate
                (evalModal
                  (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
                  w (ModalFormula.bel i phi))
                (evalModal
                  (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
                  w (ModalFormula.bel i phi))) := by
  have hBoth := strongModelEndpoints_two_walls_supports_straddle
    worlds R q0 q1 val c h0 h1 hcHalf hcOne i w phi hTwo
  rcases convexStrongModelPath_probabilityFree_crossing_order
      worlds R q0 q1 val c h0 h1 hcHalf hcOne i w hFree hTwo with
    ⟨pair, hOrder, _, _⟩
  refine ⟨pair, ?_⟩
  rcases hOrder with hPosFirst | hSim | hNegFirst
  · exact Or.inl ⟨hPosFirst,
      convexStrongModelPath_probabilityFree_positive_first_midpoint
        worlds R q0 q1 val c h0 h1 hcHalf hcOne i w hFree
        pair hBoth.1 hBoth.2 hPosFirst⟩
  · exact Or.inr (Or.inl ⟨hSim,
      convexStrongModelPath_probabilityFree_simultaneous_crossing
        worlds R q0 q1 val c h0 h1 hcHalf hcOne i w hFree pair hSim⟩)
  · exact Or.inr (Or.inr ⟨hNegFirst,
      convexStrongModelPath_probabilityFree_negative_first_midpoint
        worlds R q0 q1 val c h0 h1 hcHalf hcOne i w hFree
        pair hBoth.1 hBoth.2 hNegFirst⟩)

/-!
## Research consequence

Crossing order is now attached to an actual path of complete strong 4-PEL
models.  The two intrinsic times are not merely hits on an externally chosen
support segment: at `tp` and `tn`, the corresponding component of the modal
support coordinate of `convexStrongModelAt` equals the fixed Lockean threshold.

For non-simultaneous crossings, the rational midpoint is itself in the unit
interval and therefore defines a complete strong model. Its object-language
belief value is the forced positive-first or negative-first intermediate FDE
phase. For a simultaneous crossing, the common parameter instead realizes the
wall intersection `(c,c)` and hence the inclusive glut value `B` at one point.
Thus all three cases of the earlier affine geometry are now classified by
admissible models rather than by external support points alone.
-/

end PEL4
