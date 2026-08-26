import PEL4.ComplexRotation
import PEL4.ComplexModelPath

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
