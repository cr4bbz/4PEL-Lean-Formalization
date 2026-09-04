import PEL4.ConvexProbabilitySimplex
import PEL4.ModalDynamicsIntermediatePhase
import PEL4.PopulationAxiology.ParaconsistentComparison

namespace PEL4.PopulationAxiology

/-!
# Prospect geometry: identical classical endpoints, different middle phases

The existing probability and modal-dynamics layers verify rational convex
paths and threshold their positive and negative support coordinates
independently.  This module gives the first population-axiology-facing witness:
two affine support paths have the same classical `T` and `F` endpoints, yet
their midpoints have different four-valued phases.

* On the exclusive path, positive and negative support trade places without
  overlap.  At threshold `3/4`, the midpoint is the gap `N`.
* On the overlapping path, both endpoints retain sub-threshold support for the
  opposing side.  At the same midpoint, both coordinates reach `3/4`, yielding
  the glut `B`.

Thus convex interpolation does not by itself classicalize a comparison.  The
coarse endpoint values forget path-lift information carried by overlap.
-/

/-- A `T`-to-`F` path with exclusive positive and negative support. -/
def exclusiveComparisonPath (t : Rat) : FDEValue :=
  affineThresholdState (3 / 4) 1 0 0 1 t

/-- A `T`-to-`F` path with persistent sub-threshold opposing support. -/
def overlappingComparisonPath (t : Rat) : FDEValue :=
  affineThresholdState (3 / 4) 1 (1 / 2) (1 / 2) 1 t

/-- The exclusive path has classical endpoints. -/
theorem exclusive_path_endpoints :
    exclusiveComparisonPath 0 = FDEValue.T ∧
      exclusiveComparisonPath 1 = FDEValue.F := by
  native_decide

/-- The overlapping path has exactly the same classical endpoints. -/
theorem overlapping_path_endpoints :
    overlappingComparisonPath 0 = FDEValue.T ∧
      overlappingComparisonPath 1 = FDEValue.F := by
  native_decide

/-- The midpoint of the exclusive path is underdetermined. -/
theorem exclusive_path_midpoint_is_gap :
    exclusiveComparisonPath (1 / 2) = FDEValue.N := by
  native_decide

/-- The midpoint of the overlapping path is contradictory. -/
theorem overlapping_path_midpoint_is_glut :
    overlappingComparisonPath (1 / 2) = FDEValue.B := by
  native_decide

/-- Coarse classical endpoint data does not determine the intermediate 4-PEL
phase of an affine support path. -/
theorem same_endpoints_different_midpoint :
    exclusiveComparisonPath 0 = overlappingComparisonPath 0 ∧
    exclusiveComparisonPath 1 = overlappingComparisonPath 1 ∧
    exclusiveComparisonPath (1 / 2) ≠
      overlappingComparisonPath (1 / 2) := by
  native_decide

end PEL4.PopulationAxiology
