import PEL4.ComplexRotation
import PEL4.ComplexModelCrossing

/-!
# Focused axiom audit for the complex-coordinate publication chain

Compile this module directly with

`lake env lean PEL4/ComplexAxiomAudit.lean`

to reproduce Lean's transitive dependency report. This is intentionally a
focused audit; it does not certify older finite-model modules that still use
`native_decide`.
-/

#print axioms PEL4.supportComplexCoord_injective
#print axioms PEL4.truthInformationComplexCoord_injective
#print axioms PEL4.supportComplexCoord_squaredDistance_eq_thresholdWallCount
#print axioms PEL4.FourCellMass.thresholdGlut_iff_balance_bound
#print axioms PEL4.FourCellMass.thresholdValue_region_classification
#print axioms PEL4.ComplexCoord.I_mul_I
#print axioms PEL4.ComplexCoord.iConjugate_eq_I_mul_conj
#print axioms PEL4.truthInformationComplexCoord_conflate
#print axioms PEL4.truthInformationComplexCoord_rotate
#print axioms PEL4.rotate_not_in_klein_group
#print axioms PEL4.FourCellMass.cellBalanceCoord_rotate
#print axioms PEL4.FourCellMass.cellBalanceCoord_diamond
#print axioms PEL4.FourCellMass.four_cell_reconstruction
#print axioms PEL4.FourCellMass.thresholdValue_rotate
#print axioms PEL4.convexStrongModelAt_modalSupportComplexCoord_probabilityFree
#print axioms PEL4.thresholdWallCount_eq_two_iff
#print axioms PEL4.rat_mul_two
#print axioms PEL4.ratMidpoint_strictly_between
#print axioms PEL4.convexStrongModelAt_evalBel_probabilityFree_eq_affineThresholdState
#print axioms PEL4.convexStrongModelPath_probabilityFree_crossing_order
#print axioms PEL4.convexStrongModelPath_probabilityFree_positive_first_midpoint
#print axioms PEL4.convexStrongModelPath_probabilityFree_negative_first_midpoint
#print axioms PEL4.convexStrongModelPath_probabilityFree_simultaneous_crossing
#print axioms PEL4.convexStrongModelPath_probabilityFree_complete_crossing_classification
