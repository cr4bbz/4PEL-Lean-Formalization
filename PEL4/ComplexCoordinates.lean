import Lean.Elab.Tactic.Omega
import PEL4.ModalDynamicsGeometry

namespace PEL4

/-!
# Complex coordinates for four-valued evidence

This module gives the existing two-bit FDE semantics a dependency-free
complex-coordinate presentation. `ComplexCoord α` is deliberately only a
pair of coordinates: no complex multiplication is introduced and no logical
meaning is assigned to `i * i = -1`.

There are two useful embeddings.

* `supportComplexCoord` sends `(pos, neg)` to `pos + i neg`. Its four points
  are the vertices `0`, `1`, `i`, and `1 + i` of the threshold square.
* `truthInformationComplexCoord` changes coordinates to
  `(pos - neg) + i (pos + neg - 1)`. It sends `T`, `F`, `B`, and `N` to
  `1`, `-1`, `i`, and `-i`, respectively.

Thus the real coordinate records truth/falsity polarity, while the imaginary
coordinate records glut/gap polarity. These are verified coordinate facts;
their philosophical interpretation remains a separate research layer.
-/

/-- A dependency-free pair used as a complex coordinate. It intentionally
does not carry multiplication or field structure. -/
structure ComplexCoord (α : Type) where
  re : α
  im : α
  deriving DecidableEq, Repr

namespace ComplexCoord

/-- The integer coordinate representing `0`. -/
def zero : ComplexCoord Int := ⟨0, 0⟩

/-- The integer coordinate representing `1`. -/
def one : ComplexCoord Int := ⟨1, 0⟩

/-- The integer coordinate representing `-1`. -/
def negOne : ComplexCoord Int := ⟨-1, 0⟩

/-- The integer coordinate representing the positive imaginary unit `i`. -/
def I : ComplexCoord Int := ⟨0, 1⟩

/-- The integer coordinate representing `-i`. -/
def negI : ComplexCoord Int := ⟨0, -1⟩

/-- Coordinate action corresponding algebraically to `i * conjugate(z)`.
Only the resulting coordinate swap is part of the formalized semantics. -/
def iConjugate (z : ComplexCoord Int) : ComplexCoord Int :=
  ⟨z.im, z.re⟩

/-- Coordinate action corresponding algebraically to `-conjugate(z)`.
It reverses the real axis while preserving the imaginary axis. -/
def negConjugate (z : ComplexCoord Int) : ComplexCoord Int :=
  ⟨-z.re, z.im⟩

/-- Squared Euclidean distance on integer complex coordinates. -/
def squaredDistance (z w : ComplexCoord Int) : Int :=
  let dr := z.re - w.re
  let di := z.im - w.im
  dr * dr + di * di

/-- Two coordinates are equal when both components are equal. -/
theorem eq_of_re_im_eq {α : Type} {z w : ComplexCoord α}
    (hre : z.re = w.re) (him : z.im = w.im) : z = w := by
  rcases z with ⟨zr, zi⟩
  rcases w with ⟨wr, wi⟩
  simp only at hre him
  cases hre
  cases him
  rfl

end ComplexCoord

/-- Boolean support as an integer coordinate. -/
def supportBit : Bool → Int
  | false => 0
  | true => 1

/-- Raw support-square embedding `(pos, neg) ↦ pos + i neg`. -/
def supportComplexCoord (v : FDEValue) : ComplexCoord Int :=
  ⟨supportBit v.pos, supportBit v.neg⟩

/-- Rotated truth/information embedding
`(pos, neg) ↦ (pos - neg) + i (pos + neg - 1)`. -/
def truthInformationComplexCoord (v : FDEValue) : ComplexCoord Int :=
  ⟨supportBit v.pos - supportBit v.neg,
    supportBit v.pos + supportBit v.neg - 1⟩

@[simp] theorem supportComplexCoord_N :
    supportComplexCoord FDEValue.N = ComplexCoord.zero := by rfl

@[simp] theorem supportComplexCoord_T :
    supportComplexCoord FDEValue.T = ComplexCoord.one := by rfl

@[simp] theorem supportComplexCoord_F :
    supportComplexCoord FDEValue.F = ComplexCoord.I := by rfl

@[simp] theorem supportComplexCoord_B :
    supportComplexCoord FDEValue.B = ⟨1, 1⟩ := by rfl

@[simp] theorem truthInformationComplexCoord_T :
    truthInformationComplexCoord FDEValue.T = ComplexCoord.one := by rfl

@[simp] theorem truthInformationComplexCoord_F :
    truthInformationComplexCoord FDEValue.F = ComplexCoord.negOne := by rfl

@[simp] theorem truthInformationComplexCoord_B :
    truthInformationComplexCoord FDEValue.B = ComplexCoord.I := by rfl

@[simp] theorem truthInformationComplexCoord_N :
    truthInformationComplexCoord FDEValue.N = ComplexCoord.negI := by rfl

/-- The raw support-square embedding loses no categorical FDE information. -/
theorem supportComplexCoord_injective :
    Function.Injective supportComplexCoord := by
  intro a b
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-- The truth/information embedding also loses no categorical FDE
information. -/
theorem truthInformationComplexCoord_injective :
    Function.Injective truthInformationComplexCoord := by
  intro a b
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-- In raw support coordinates, FDE negation is the coordinate action
`i * conjugate(z)`: it swaps positive and negative support. -/
theorem supportComplexCoord_not (v : FDEValue) :
    supportComplexCoord (FDEValue.not v) =
      ComplexCoord.iConjugate (supportComplexCoord v) := by
  rcases v with ⟨p, n⟩
  cases p <;> cases n <;> rfl

/-- In truth/information coordinates, FDE negation is `-conjugate(z)`:
truth polarity reverses, while glut/gap polarity is preserved. -/
theorem truthInformationComplexCoord_not (v : FDEValue) :
    truthInformationComplexCoord (FDEValue.not v) =
      ComplexCoord.negConjugate (truthInformationComplexCoord v) := by
  rcases v with ⟨p, n⟩
  cases p <;> cases n <;> rfl

/-- The existing combinatorial threshold-wall distance is exactly the squared
Euclidean distance between raw complex support coordinates. -/
theorem supportComplexCoord_squaredDistance_eq_thresholdWallCount
    (a b : FDEValue) :
    ComplexCoord.squaredDistance
        (supportComplexCoord a) (supportComplexCoord b) =
      Int.ofNat (thresholdWallCount a b) := by
  rcases a with ⟨ap, an⟩
  rcases b with ⟨bp, bn⟩
  cases ap <;> cases an <;> cases bp <;> cases bn <;> native_decide

/-!
## Four-cell evidence masses

The next structure records a finite `T/B/N/F` partition for one formula. It
is independent of the legacy weak `ProbMeasure` interface and can therefore
state exactly which probability-integrity assumption the decomposition uses.
-/

/-- Finite masses of the four exhaustive FDE cells for one formula. -/
structure FourCellMass where
  t : Nat
  b : Nat
  n : Nat
  f : Nat
  total : Nat
  normalized : t + b + n + f = total

namespace FourCellMass

/-- Mass with positive support. -/
def positive (s : FourCellMass) : Nat := s.t + s.b

/-- Mass with negative support. -/
def negative (s : FourCellMass) : Nat := s.f + s.b

/-- Truth/information coordinates obtained from the two support masses. -/
def supportBalanceCoord (s : FourCellMass) : ComplexCoord Int :=
  ⟨Int.ofNat s.positive - Int.ofNat s.negative,
    Int.ofNat s.positive + Int.ofNat s.negative - Int.ofNat s.total⟩

/-- The same coordinates read directly from the four FDE cells. -/
def cellBalanceCoord (s : FourCellMass) : ComplexCoord Int :=
  ⟨Int.ofNat s.t - Int.ofNat s.f,
    Int.ofNat s.b - Int.ofNat s.n⟩

/-- The support-plane coordinate transformation decomposes into truth balance
`T - F` and conflict/ignorance balance `B - N`. -/
theorem supportBalanceCoord_eq_cellBalanceCoord (s : FourCellMass) :
    s.supportBalanceCoord = s.cellBalanceCoord := by
  apply ComplexCoord.eq_of_re_im_eq
  · simp [supportBalanceCoord, cellBalanceCoord, positive, negative]
    omega
  · simp [supportBalanceCoord, cellBalanceCoord, positive, negative]
    have htotal := s.normalized
    omega

/-- Threshold-glut condition for a finite four-cell profile. -/
def IsThresholdGlut (s : FourCellMass) (k : Nat) : Prop :=
  k ≤ s.positive ∧ k ≤ s.negative

/-- Dependency-free natural-number absolute difference. -/
def absDiff (a b : Nat) : Nat :=
  (a - b) + (b - a)

/-- A threshold glut forces not only the usual overlap lower bound, but a
sharper balance-sensitive bound. Gap mass and unequal strict T/F mass both
require additional B mass:

`2k + N + |T-F| ≤ total + B`.
-/
theorem thresholdGlut_balance_bound
    (s : FourCellMass) (k : Nat)
    (h : s.IsThresholdGlut k) :
    2 * k + s.n + absDiff s.t s.f ≤ s.total + s.b := by
  rcases h with ⟨hpos, hneg⟩
  have htotal := s.normalized
  change k ≤ s.t + s.b at hpos
  change k ≤ s.f + s.b at hneg
  unfold absDiff
  omega

/-- The established coarse overlap bound follows by forgetting the additional
gap and strict-polarity terms. -/
theorem thresholdGlut_overlap_bound
    (s : FourCellMass) (k : Nat)
    (h : s.IsThresholdGlut k) :
    2 * k ≤ s.total + s.b := by
  have hsharp := thresholdGlut_balance_bound s k h
  omega

end FourCellMass

/-!
## Research boundary

The verified content is coordinate algebra, injectivity at the four categorical
vertices, the metric correspondence, the four-cell decomposition, and the
balance-sensitive glut inequality. The module does **not** claim that complex
multiplication is a logical connective, that evidence is a quantum amplitude,
or that the two-dimensional coordinate determines the full four-cell
distribution.

Indeed, the mass coordinate retains only `T - F` and `B - N`; distinct
four-cell distributions may share it. This makes the construction a precise
instance of the repository's broader theme of projection and structural
transport rather than a replacement for the richer evidence state.
-/

end PEL4
