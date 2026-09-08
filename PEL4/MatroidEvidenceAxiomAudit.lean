import PEL4.MatroidEvidence

namespace PEL4

/-!
Declaration-level trust inventory for the matroid-evidence gate.
The CI log should show only standard Lean axioms for these declarations.
-/

#print axioms channelMatroid
#print axioms samePolarity_iff_mem_singletonClosure
#print axioms supportsChannel_channelClosure_iff
#print axioms realizesFDE_channelClosure_iff
#print axioms realizesFDE_B_iff
#print axioms channelRank_N
#print axioms channelRank_T
#print axioms channelRank_F
#print axioms channelRank_B

end PEL4
