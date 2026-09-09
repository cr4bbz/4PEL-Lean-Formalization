import PEL4.ClassicalRecovery

/-!
# Gate 5 axiom audit

Selected recovery claims are printed here so CI can keep the new classicality
layer inside the repository's explicit trust boundary.
-/

#print axioms PEL4.realizesFDE_gapFree_iff_channelComplete
#print axioms PEL4.realizesFDE_glutFree_iff_channelConsistent
#print axioms PEL4.evidentiallyRegularValue_iff_classical
#print axioms PEL4.realizesFDE_channelRegular_iff_classical
#print axioms PEL4.classicalValue_not
#print axioms PEL4.classicalValue_and
#print axioms PEL4.classicalValue_or
#print axioms PEL4.excludedMiddle_designated_iff_gapFree
#print axioms PEL4.excludedMiddle_eq_T_iff_classical
#print axioms PEL4.realizesFDE_channelRegular_restores_strict_LEM
#print axioms PEL4.contradiction_designated_iff_glut
#print axioms PEL4.glutFree_restores_LP_explosion
#print axioms PEL4.realizesFDE_channelConsistency_restores_LP_explosion
#print axioms PEL4.stable_regular_value_is_classical_through_accessibility
