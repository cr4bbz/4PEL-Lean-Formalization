import PEL4.PopulationAxiology.RiskyCompensation
import PEL4.PopulationAxiology.RiskyCompensationInstance
import PEL4.PopulationAxiology.ProspectGeometry

/-!
# Focused axiom audit for the finite fine-grainedness / 4-PEL bridge

Compile this module with `lake env lean` to display the transitive assumptions
of the publication-facing Gate 2 theorem chain. The older affine prospect-
geometry witnesses remain outside this audit because their closed rational
computations currently use `native_decide`.
-/

#print axioms PEL4.PopulationAxiology.FiniteStepChain.transport
#print axioms PEL4.PopulationAxiology.global_transport_of_finiteFineGrained
#print axioms PEL4.PopulationAxiology.sameTierSlight_not_finitely_fine_grained
#print axioms PEL4.PopulationAxiology.finite_chain_axiological_glut
#print axioms PEL4.PopulationAxiology.FourCellProbability.pureB_thresholdValue
#print axioms PEL4.PopulationAxiology.finiteWitnessKernel_conflict_without_triviality
#print axioms PEL4.PopulationAxiology.ExactStepChain.transport
#print axioms PEL4.PopulationAxiology.reciprocalRiskTransport
#print axioms PEL4.PopulationAxiology.reciprocalRisk_axiological_glut
#print axioms PEL4.PopulationAxiology.toy_risky_comparison_is_glut
#print axioms PEL4.PopulationAxiology.toy_unrelated_comparison_is_gap
#print axioms PEL4.PopulationAxiology.riskShiftProspect_pair_valid
#print axioms PEL4.PopulationAxiology.gate3_generated_rgnep
#print axioms PEL4.PopulationAxiology.gate3_prospects_valid
#print axioms PEL4.PopulationAxiology.gate3_exact_two_step_chain
#print axioms PEL4.PopulationAxiology.gate3ReciprocalRiskChain
#print axioms PEL4.PopulationAxiology.gate3_kernel_endpoint_shape
#print axioms PEL4.PopulationAxiology.gate3_kernel_coupled_endpoint
