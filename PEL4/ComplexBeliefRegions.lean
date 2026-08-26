import Lean.Elab.Tactic.Omega
import PEL4.ComplexCoordinates

namespace PEL4

/-!
# Exact threshold regions in truth/information coordinates

`ComplexCoordinates` identifies the real balance `T - F` and the imaginary
balance `B - N`.  This module turns that representation into an exact phase
classifier for finite scaled evidence profiles.

For a normalized profile, adding the total mass to the imaginary balance and
then adding or subtracting the real balance recovers twice the positive or
negative support mass.  Comparing those two expressions with twice the
threshold therefore partitions the coordinate plane into the four FDE phases.
-/

namespace FourCellMass

/-- The categorical threshold value determined by the two support masses.
The threshold is integer-scaled so the phase geometry remains in one ordered
additive domain. -/
def thresholdValue (s : FourCellMass) (k : Int) : FDEValue :=
  { pos := decide (k ≤ Int.ofNat s.positive)
  , neg := decide (k ≤ Int.ofNat s.negative) }

/-- Both signed support masses meet the integer-scaled threshold. -/
def IsThresholdGlutAt (s : FourCellMass) (k : Int) : Prop :=
  k ≤ Int.ofNat s.positive ∧ k ≤ Int.ofNat s.negative

/-- Truth-only threshold phase. -/
def IsThresholdTruth (s : FourCellMass) (k : Int) : Prop :=
  k ≤ Int.ofNat s.positive ∧ Int.ofNat s.negative < k

/-- Falsity-only threshold phase. -/
def IsThresholdFalsity (s : FourCellMass) (k : Int) : Prop :=
  Int.ofNat s.positive < k ∧ k ≤ Int.ofNat s.negative

/-- Neither-support threshold phase. -/
def IsThresholdGap (s : FourCellMass) (k : Int) : Prop :=
  Int.ofNat s.positive < k ∧ Int.ofNat s.negative < k

/-- Coordinate expression equal to twice the positive support mass. -/
def doubledPositiveCoordinate (s : FourCellMass) : Int :=
  Int.ofNat s.total + s.cellBalanceCoord.im + s.cellBalanceCoord.re

/-- Coordinate expression equal to twice the negative support mass. -/
def doubledNegativeCoordinate (s : FourCellMass) : Int :=
  Int.ofNat s.total + s.cellBalanceCoord.im - s.cellBalanceCoord.re

theorem doubledPositiveCoordinate_eq (s : FourCellMass) :
    s.doubledPositiveCoordinate = 2 * Int.ofNat s.positive := by
  have htotal := s.normalized
  simp [doubledPositiveCoordinate, cellBalanceCoord, positive]
  omega

theorem doubledNegativeCoordinate_eq (s : FourCellMass) :
    s.doubledNegativeCoordinate = 2 * Int.ofNat s.negative := by
  have htotal := s.normalized
  simp [doubledNegativeCoordinate, cellBalanceCoord, negative]
  omega

/-- Region above both threshold walls: the glut phase. -/
def InGlutRegion (s : FourCellMass) (k : Int) : Prop :=
  2 * k ≤ s.doubledPositiveCoordinate ∧
    2 * k ≤ s.doubledNegativeCoordinate

/-- Region above only the positive threshold wall. -/
def InTruthRegion (s : FourCellMass) (k : Int) : Prop :=
  2 * k ≤ s.doubledPositiveCoordinate ∧
    s.doubledNegativeCoordinate < 2 * k

/-- Region above only the negative threshold wall. -/
def InFalsityRegion (s : FourCellMass) (k : Int) : Prop :=
  s.doubledPositiveCoordinate < 2 * k ∧
    2 * k ≤ s.doubledNegativeCoordinate

/-- Region below both threshold walls: the gap phase. -/
def InGapRegion (s : FourCellMass) (k : Int) : Prop :=
  s.doubledPositiveCoordinate < 2 * k ∧
    s.doubledNegativeCoordinate < 2 * k

theorem thresholdGlut_iff_complexRegion (s : FourCellMass) (k : Int) :
    s.IsThresholdGlutAt k ↔ s.InGlutRegion k := by
  rw [InGlutRegion, doubledPositiveCoordinate_eq,
    doubledNegativeCoordinate_eq]
  unfold IsThresholdGlutAt
  omega

theorem thresholdTruth_iff_complexRegion (s : FourCellMass) (k : Int) :
    s.IsThresholdTruth k ↔ s.InTruthRegion k := by
  rw [InTruthRegion, doubledPositiveCoordinate_eq,
    doubledNegativeCoordinate_eq]
  unfold IsThresholdTruth
  omega

theorem thresholdFalsity_iff_complexRegion (s : FourCellMass) (k : Int) :
    s.IsThresholdFalsity k ↔ s.InFalsityRegion k := by
  rw [InFalsityRegion, doubledPositiveCoordinate_eq,
    doubledNegativeCoordinate_eq]
  unfold IsThresholdFalsity
  omega

theorem thresholdGap_iff_complexRegion (s : FourCellMass) (k : Int) :
    s.IsThresholdGap k ↔ s.InGapRegion k := by
  rw [InGapRegion, doubledPositiveCoordinate_eq,
    doubledNegativeCoordinate_eq]
  unfold IsThresholdGap
  omega

/-- The four coordinate regions classify the actual FDE threshold value. -/
theorem thresholdValue_region_classification
    (s : FourCellMass) (k : Int) :
    (s.thresholdValue k = FDEValue.T ↔ s.InTruthRegion k) ∧
    (s.thresholdValue k = FDEValue.F ↔ s.InFalsityRegion k) ∧
    (s.thresholdValue k = FDEValue.B ↔ s.InGlutRegion k) ∧
    (s.thresholdValue k = FDEValue.N ↔ s.InGapRegion k) := by
  have hT : s.thresholdValue k = FDEValue.T ↔ s.IsThresholdTruth k := by
    simp [thresholdValue, IsThresholdTruth, FDEValue.T, positive, negative]
  have hF : s.thresholdValue k = FDEValue.F ↔ s.IsThresholdFalsity k := by
    simp [thresholdValue, IsThresholdFalsity, FDEValue.F, positive, negative]
  have hB : s.thresholdValue k = FDEValue.B ↔ s.IsThresholdGlutAt k := by
    simp [thresholdValue, IsThresholdGlutAt, FDEValue.B, positive, negative]
  have hN : s.thresholdValue k = FDEValue.N ↔ s.IsThresholdGap k := by
    simp [thresholdValue, IsThresholdGap, FDEValue.N, positive, negative]
  exact ⟨hT.trans (thresholdTruth_iff_complexRegion s k),
    hF.trans (thresholdFalsity_iff_complexRegion s k),
    hB.trans (thresholdGlut_iff_complexRegion s k),
    hN.trans (thresholdGap_iff_complexRegion s k)⟩

end FourCellMass

end PEL4
