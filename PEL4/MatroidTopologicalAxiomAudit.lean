import PEL4.MatroidTopologicalSierpinski

namespace PEL4

/-!
Declaration-level trust inventory for Matroid Evidence Gate 2.
The CI log records the exact Lean axioms used by the bridge and obstruction
results rather than silently upgrading classical topological reasoning to a
constructive claim.
-/

#print axioms closure_empty_not_mem
#print axioms topologicalClosureExchange_iff_r0Like
#print axioms topologicalMatroidClosure
#print axioms channelInteriorSemantics_closure_iff_channelClosure
#print axioms channelInteriorSemantics_r0Like
#print axioms channelInteriorSemantics_exchange
#print axioms sierpinski_focus_specializes_neighbour
#print axioms sierpinski_neighbour_not_specializes_focus
#print axioms sierpinski_not_topologicalR0Like
#print axioms sierpinski_not_topologicalClosureExchange

end PEL4
