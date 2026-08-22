import PEL4.ConvexProbabilitySimplex
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Convex model-valued probability paths

C17A strengthened the local finite-probability contract. C17B generated valid
local measures from normalized nonnegative world weights. C17C proved that
rational convex interpolation preserves those distributions and that every
fixed event mass varies affinely.

This module lifts that probability-layer path into the full legacy 4-PEL
`Model` structure while keeping the non-probabilistic semantic skeleton fixed.
For a fixed world list, accessibility relation, valuation, and Lockean
threshold, only the local weight field and hence `mu` varies.

The resulting path is certified as a `StrongProbabilityModel` at every
rational parameter `0 <= t <= 1`.

A crucial boundary remains explicit: the affine event-mass theorem applies to
a fixed event list. For a general modal formula containing probabilistic belief,
the set of positive or negative worlds may itself vary with `t`. A later gate
will therefore lift the threshold-crossing geometry first for events whose
membership is fixed along the path.
-/

/-- Build a complete legacy 4-PEL model from a local normalized nonnegative
weight distribution at every agent/world pair. -/
def weightGeneratedModel
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (weight : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (hDist : ∀ i w, FiniteWeightDistribution (R i w) (weight i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1) :
    Model W Ag Atom :=
  { worlds := worlds
    R := R
    mu := fun i w => weightGeneratedMeasure (R i w) (weight i w)
    val := val
    c := c
    mu_total := by
      intro i w
      simpa [weightGeneratedMeasure] using (hDist i w).total
    mu_empty := by
      intro i w
      simpa [weightGeneratedMeasure] using
        weightedEventMass_empty (R i w) (weight i w)
    c_gt_half := hcHalf
    c_le_one := hcOne }

/-- Every model built from local finite weight distributions satisfies the
strong probability integrity layer. -/
theorem weightGeneratedModel_probabilityIntegrity
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (weight : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (hDist : ∀ i w, FiniteWeightDistribution (R i w) (weight i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1) :
    ModelProbabilityIntegrity
      (weightGeneratedModel worlds R weight val c hDist hcHalf hcOne) := by
  intro i w
  change FiniteProbabilityIntegrity
    (weightGeneratedMeasure (R i w) (weight i w)) (R i w)
  exact weightGeneratedMeasure_integrity (R i w) (weight i w) (hDist i w)

/-- Package a weight-generated model immediately as a strong probability
model. -/
def strongWeightGeneratedModel
    {W Ag Atom : Type} [DecidableEq W]
    (worlds : FiniteSet W)
    (R : Ag → W → FiniteSet W)
    (weight : Ag → W → W → Rat)
    (val : W → Atom → FDEValue)
    (c : Ag → Rat)
    (hDist : ∀ i w, FiniteWeightDistribution (R i w) (weight i w))
    (hcHalf : ∀ i, c i > 1/2)
    (hcOne : ∀ i, c i ≤ 1) :
    StrongProbabilityModel W Ag Atom :=
  { toModel := weightGeneratedModel worlds R weight val c hDist hcHalf hcOne
    probability_integrity :=
      weightGeneratedModel_probabilityIntegrity
        worlds R weight val c hDist hcHalf hcOne }

/-- Pointwise interpolation of an entire field of local world weights. -/
def convexLocalWeights
    {W Ag : Type}
    (t : Rat)
    (q0 q1 : Ag → W → W → Rat) :
    Ag → W → W → Rat :=
  fun i w => convexWeight t (q0 i w) (q1 i w)

/-- Every rational unit-interval point between two local weight fields defines
a complete strong 4-PEL model on the same semantic skeleton. -/
def convexStrongModelAt
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
    (t : Rat)
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    StrongProbabilityModel W Ag Atom :=
  strongWeightGeneratedModel
    worlds R (convexLocalWeights t q0 q1) val c
    (fun i w =>
      convexWeightDistribution
        (R i w) (q0 i w) (q1 i w)
        (h0 i w) (h1 i w) t ht0 ht1)
    hcHalf hcOne

/-- The model path fixes the world list exactly. -/
theorem convexStrongModelAt_worlds
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
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel.worlds = worlds := by
  rfl

/-- Accessibility is constant along the model-valued path. -/
theorem convexStrongModelAt_accessibility
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
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel.R = R := by
  rfl

/-- Atomic valuation is constant along the model-valued path. -/
theorem convexStrongModelAt_valuation
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
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel.val = val := by
  rfl

/-- Lockean thresholds are constant along the model-valued path. -/
theorem convexStrongModelAt_threshold
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
    (t : Rat) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel.c = c := by
  rfl

/-- Every fixed local event has exactly affine probability mass along the full
model-valued path. -/
theorem convexStrongModelAt_eventMass
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
    (i : Ag) (w : W) (event : FiniteSet W) :
    (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1).toModel.mu i w event =
      (1 - t) * weightGeneratedMeasure (R i w) (q0 i w) event +
        t * weightGeneratedMeasure (R i w) (q1 i w) event := by
  change
    weightedEventMass (R i w) (convexWeight t (q0 i w) (q1 i w)) event =
      (1 - t) * weightedEventMass (R i w) (q0 i w) event +
        t * weightedEventMass (R i w) (q1 i w) event
  exact weightedEventMass_convex (R i w) (q0 i w) (q1 i w) event t

/-!
## Research consequence

If this gate compiles, the project has an actual rational path of complete
probabilistically certified 4-PEL models. Worlds, accessibility, valuation, and
threshold remain fixed; only local probability changes. Moreover every fixed
event mass along that model path is exactly affine in the path parameter.

This closes the gap between a probability-simplex path and a model-valued path.
It does not yet close the final formula-level gap for arbitrary modal formulas,
because a probability-sensitive formula can change the event whose mass is
being measured. The next lift should therefore begin with atomic or otherwise
path-invariant events and then determine the maximal formula fragment for which
support-event membership is fixed.
-/

end PEL4
