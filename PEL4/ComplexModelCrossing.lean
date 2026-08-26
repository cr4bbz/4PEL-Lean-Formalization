import PEL4.ComplexModelPath
import PEL4.ModalDynamicsCrossingOrder

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
  simp [affineRatPath, Rat.sub_eq_add_neg, Rat.mul_add,
    Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

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
    simpa [m0, m1, z0, z1,
      evalModal_bel_eq_modalSupportComplexThresholdState] using hTwo
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

/-!
## Research consequence

Crossing order is now attached to an actual path of complete strong 4-PEL
models.  The two intrinsic times are not merely hits on an externally chosen
support segment: at `tp` and `tn`, the corresponding component of the modal
support coordinate of `convexStrongModelAt` equals the fixed Lockean threshold.

The next theorem can evaluate the midpoint strong model and identify its
belief value with the already verified positive-first or negative-first
intermediate FDE phase.
-/

end PEL4
