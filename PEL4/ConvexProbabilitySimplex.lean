import PEL4.WeightGeneratedProbability
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Convex rational paths in the finite probability simplex

C17A introduced a stronger finite-probability integrity contract. C17B then
showed that normalized nonnegative rational point weights generate measures
satisfying that contract. This module proves the next structural fact: on a
fixed finite support, the rational convex interpolation of two valid weight
distributions is again a valid weight distribution.

For `0 <= t <= 1`, define

```text
q_t(x) = (1 - t) * q_0(x) + t * q_1(x).
```

The central results are:

* pointwise nonnegativity is preserved;
* every generated event mass is the same convex interpolation of the endpoint
  event masses;
* total mass therefore remains one;
* hence the full rational line segment between two finite weight distributions
  lies inside the finite probability simplex;
* every point on that segment generates a measure satisfying
  `FiniteProbabilityIntegrity`.

This is still a path in the probability layer. The later model-realizability
gate must package these local distributions into complete 4-PEL models with
fixed relation, valuation, and threshold.
-/

/-- Pointwise rational convex interpolation of two weight functions. -/
def convexWeight {W : Type}
    (t : Rat) (q0 q1 : W → Rat) : W → Rat :=
  fun x => (1 - t) * q0 x + t * q1 x

/-- At `t = 0`, convex interpolation returns the source weight. -/
theorem convexWeight_zero
    {W : Type}
    (q0 q1 : W → Rat) :
    convexWeight 0 q0 q1 = q0 := by
  funext x
  simp [convexWeight, Rat.sub_eq_add_neg, Rat.add_zero]

/-- At `t = 1`, convex interpolation returns the target weight. -/
theorem convexWeight_one
    {W : Type}
    (q0 q1 : W → Rat) :
    convexWeight 1 q0 q1 = q1 := by
  funext x
  simp [convexWeight, Rat.sub_self, Rat.zero_add]

/-- Convex interpolation preserves pointwise nonnegativity on the unit
interval. -/
theorem convexWeight_nonnegative
    {W : Type}
    (t : Rat) (q0 q1 : W → Rat)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : W)
    (hq0 : 0 ≤ q0 x)
    (hq1 : 0 ≤ q1 x) :
    0 ≤ convexWeight t q0 q1 x := by
  have hOneMinus : 0 ≤ 1 - t :=
    (Rat.le_iff_sub_nonneg t 1).1 ht1
  exact Rat.add_nonneg
    (Rat.mul_nonneg hOneMinus hq0)
    (Rat.mul_nonneg ht0 hq1)

/-- Weight-generated event mass is linear in the weight function. In
particular, every event mass along the convex weight path is the convex
interpolation of its endpoint masses. -/
theorem weightedEventMass_convex
    {W : Type} [DecidableEq W]
    (support : FiniteSet W)
    (q0 q1 : W → Rat)
    (event : FiniteSet W)
    (t : Rat) :
    weightedEventMass support (convexWeight t q0 q1) event =
      (1 - t) * weightedEventMass support q0 event +
        t * weightedEventMass support q1 event := by
  induction support with
  | nil =>
      simp [weightedEventMass, Rat.mul_zero, Rat.add_zero]
  | cons x xs ih =>
      by_cases hx : x ∈ event
      · simp [weightedEventMass, convexWeight, hx, ih,
          Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
      · simp [weightedEventMass, convexWeight, hx, ih,
          Rat.mul_zero, Rat.zero_add]

/-- The full rational line segment between two normalized nonnegative weight
distributions on the same finite support remains inside that simplex. -/
theorem convexWeightDistribution
    {W : Type} [DecidableEq W]
    (support : FiniteSet W)
    (q0 q1 : W → Rat)
    (h0 : FiniteWeightDistribution support q0)
    (h1 : FiniteWeightDistribution support q1)
    (t : Rat)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    FiniteWeightDistribution support (convexWeight t q0 q1) := by
  refine
    { support_nodup := h0.support_nodup
      nonnegative := ?_
      total := ?_ }
  · intro x hx
    exact convexWeight_nonnegative t q0 q1 ht0 ht1 x
      (h0.nonnegative x hx)
      (h1.nonnegative x hx)
  · rw [weightedEventMass_convex support q0 q1 support t,
      h0.total, h1.total]
    simp only [Rat.mul_one]
    exact Rat.sub_add_cancel

/-- Every point of the convex distribution path therefore generates a local
measure satisfying the stronger finite-probability integrity contract. -/
theorem convexWeightGeneratedMeasure_integrity
    {W : Type} [DecidableEq W]
    (support : FiniteSet W)
    (q0 q1 : W → Rat)
    (h0 : FiniteWeightDistribution support q0)
    (h1 : FiniteWeightDistribution support q1)
    (t : Rat)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    FiniteProbabilityIntegrity
      (weightGeneratedMeasure support (convexWeight t q0 q1)) support := by
  exact weightGeneratedMeasure_integrity support (convexWeight t q0 q1)
    (convexWeightDistribution support q0 q1 h0 h1 t ht0 ht1)

/-!
## Research consequence

If this gate compiles, the finite probability simplex is no longer merely a
geometric interpretation. Lean will verify that every rational parameter on
the segment between two valid finite distributions is itself a valid
distribution, and that every event mass travels affinely along that segment.

The next gate can exploit `weightedEventMass_convex` to identify the positive
and negative belief-support coordinates of intermediate full models with the
affine support paths already studied by `ModalDynamicsAffineCrossing`,
`ModalDynamicsCrossingOrder`, and `ModalDynamicsIntermediatePhase`.
-/

end PEL4
