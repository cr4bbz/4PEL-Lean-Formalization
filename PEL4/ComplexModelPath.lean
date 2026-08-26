import PEL4.ComplexCoordinates
import PEL4.ConvexModelSupport

namespace PEL4

/-!
# Affine complex support coordinates on strong model paths

`ConvexModelSupport` proves separately that the positive and negative support
masses of every probability-free modal formula are affine along
`convexStrongModelAt`.  This module packages those two scalar results into the
single rational coordinate

`m⁺ + i m⁻`.

The symbol `i` remains coordinate notation: `ComplexCoord Rat` is a pair and
does not introduce complex multiplication into the object logic.  The theorem
below is nevertheless the exact affine path identity

`z(t) = (1 - t) z(0) + t z(1)`

read componentwise.
-/

namespace ComplexCoord

/-- Componentwise affine interpolation of rational complex coordinates. -/
def affine (t : Rat) (z0 z1 : ComplexCoord Rat) : ComplexCoord Rat :=
  ⟨(1 - t) * z0.re + t * z1.re,
    (1 - t) * z0.im + t * z1.im⟩

@[simp] theorem affine_re (t : Rat) (z0 z1 : ComplexCoord Rat) :
    (affine t z0 z1).re = (1 - t) * z0.re + t * z1.re := by
  rfl

@[simp] theorem affine_im (t : Rat) (z0 z1 : ComplexCoord Rat) :
    (affine t z0 z1).im = (1 - t) * z0.im + t * z1.im := by
  rfl

end ComplexCoord

/-- The raw complex support coordinate of a modal formula at an agent/world
pair.  Its real component is positive support mass and its imaginary component
is negative support mass. -/
def modalSupportComplexCoord
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : ComplexCoord Rat :=
  ⟨modalPositiveBeliefMass m i w phi,
    modalNegativeBeliefMass m i w phi⟩

@[simp] theorem modalSupportComplexCoord_re
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    (modalSupportComplexCoord m i w phi).re =
      modalPositiveBeliefMass m i w phi := by
  rfl

@[simp] theorem modalSupportComplexCoord_im
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) :
    (modalSupportComplexCoord m i w phi).im =
      modalNegativeBeliefMass m i w phi := by
  rfl

/-- Every probability-free modal formula traces an exact affine complex
support path through complete strong probability models. -/
theorem convexStrongModelAt_modalSupportComplexCoord_probabilityFree
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
    modalSupportComplexCoord
        (convexStrongModelAt worlds R q0 q1 val c h0 h1 hcHalf hcOne
          t ht0 ht1).toModel i w phi =
      ComplexCoord.affine t
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q0 val c h0 hcHalf hcOne)
          i w phi)
        (modalSupportComplexCoord
          (weightGeneratedModel worlds R q1 val c h1 hcHalf hcOne)
          i w phi) := by
  apply ComplexCoord.eq_of_re_im_eq
  · exact convexStrongModelAt_positiveBeliefMass_probabilityFree
      worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1 i w hFree
  · exact convexStrongModelAt_negativeBeliefMass_probabilityFree
      worlds R q0 q1 val c h0 h1 hcHalf hcOne
      t ht0 ht1 i w hFree

/-!
## Research consequence

The probability-free modal fragment now has a genuine model-level complex
kinematics.  The coordinate path is not merely compatible with two affine
scalar mass theorems: it is itself a Lean-verified affine path in
`ComplexCoord Rat` through complete strong models.

The next gate can transport threshold-wall crossing, crossing order, and
intermediate-phase results to this packaged model coordinate.  Formulas
containing `bel` remain outside the theorem because their formula-defined
support events can move as probability changes.
-/

end PEL4
