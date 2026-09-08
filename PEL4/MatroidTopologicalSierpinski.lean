import PEL4.MatroidTopologicalBridge
import PEL4.TopologicalEvidenceSierpinski

namespace PEL4

/-!
# Gate 2 witness: Sierpinski topology is not matroidal

The two-point Sierpinski semantics already used by the topological 4-PEL layer
has an asymmetric singleton-closure relation.  The `focus` point lies in the
closure of the `neighbour` singleton, but not conversely.  By the Gate-2
characterization this is exactly the obstruction to matroid exchange.
-/

/-- `focus` specializes to `neighbour` in the repository's Sierpinski topology. -/
theorem sierpinski_focus_specializes_neighbour :
    topologicalSpecializes SierpinskiInteriorSemantics
      SierpinskiPoint.focus SierpinskiPoint.neighbour := by
  unfold topologicalSpecializes
  apply (sierpinski_closure_focus_iff
    (EvidenceSet.singleton SierpinskiPoint.neighbour)).2
  exact Or.inr rfl

/-- The reverse specialization does not hold. -/
theorem sierpinski_neighbour_not_specializes_focus :
    ¬ topologicalSpecializes SierpinskiInteriorSemantics
      SierpinskiPoint.neighbour SierpinskiPoint.focus := by
  intro h
  unfold topologicalSpecializes at h
  have hPoint :=
    (sierpinski_closure_neighbour_iff
      (EvidenceSet.singleton SierpinskiPoint.focus)).1 h
  change SierpinskiPoint.neighbour = SierpinskiPoint.focus at hPoint
  cases hPoint

/-- The Sierpinski witness fails the R0-like singleton symmetry condition. -/
theorem sierpinski_not_topologicalR0Like :
    ¬ TopologicalR0Like SierpinskiInteriorSemantics := by
  intro hR0
  exact sierpinski_neighbour_not_specializes_focus
    (hR0 SierpinskiPoint.focus SierpinskiPoint.neighbour
      sierpinski_focus_specializes_neighbour)

/-- Therefore its topological closure cannot satisfy matroid exchange. -/
theorem sierpinski_not_topologicalClosureExchange :
    ¬ TopologicalClosureExchange SierpinskiInteriorSemantics := by
  intro hExchange
  exact sierpinski_not_topologicalR0Like
    ((topologicalClosureExchange_iff_r0Like
      SierpinskiInteriorSemantics).1 hExchange)

end PEL4
