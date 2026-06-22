import PEL4.Weatherson

namespace PEL4

/-- A representation of an edge in a relational graph. -/
structure Edge where
  id : Nat
  deriving DecidableEq, Repr

/-- A relational graph is an open menu of candidate edges. -/
abbrev RelGraph := Menu Edge

/-- A geometric graph is the set of edges that passed the projector. -/
abbrev GeomGraph := Menu Edge

/-- In RZS-ELCL, an edge might lose its geometric validity if the surrounding 
    relational context introduces "shortcuts" or "contaminants". 
    We mock this topological property: Edge 1 forms a stable geometry,
    unless both Edge 3 and Edge 4 are present to form an unphysical shortcut. -/
def has_shortcut (e : Edge) (context : RelGraph) : Bool :=
  e.id == 1 ∧ (context.any (fun x => x.id == 3)) ∧ (context.any (fun x => x.id == 4))

/-- The clique/nerve support calculates if an edge is supported by stable geometry (e.g. 4-simplices). -/
def stable_support (e : Edge) (context : RelGraph) : Nat :=
  if has_shortcut e context then 0 else 3

/-- The BRQ projector from Romero (2026).
    Evaluates whether an edge is geometrically admissible relative to the menu. -/
def Pi_BRQ (context : RelGraph) : GeomGraph :=
  context.filter (fun e => stable_support e context ≥ 3)

end PEL4
