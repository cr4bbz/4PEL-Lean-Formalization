import PEL4.Weatherson
import PEL4.Geometry

namespace PEL4

/-- 
  Theorem: The BRQ Projector violates Weatherson's Expansion Property (γ).
  This establishes that geometric projection from relational graphs is a non-binary, 
  menu-dependent choice function. It formally links Romero (2026) and Weatherson (2026),
  proving that geometry extraction is an ex-ante choice process, not a pairwise ex-post filter.
-/
theorem Pi_BRQ_violates_gamma : ¬ SatisfiesGamma Pi_BRQ := by
  -- We prove by contradiction. Assume Pi_BRQ satisfies Gamma.
  intro hGamma
  
  -- Construct our counterexample menus
  let e1 := Edge.mk 1
  let e3 := Edge.mk 3
  let e4 := Edge.mk 4
  
  let S := [e1, e3]
  let T := [e1, e4]
  
  -- By the assumption hGamma, if e1 is in Pi_BRQ S and Pi_BRQ T, it must be in Pi_BRQ (S ++ T)
  have h_S_T : e1 ∈ Pi_BRQ S → e1 ∈ Pi_BRQ T → e1 ∈ Pi_BRQ (S ++ T) := 
    hGamma e1 S T

  -- Step 1: Prove e1 ∈ Pi_BRQ S
  have h_in_S : e1 ∈ Pi_BRQ S := by
    -- Pi_BRQ S filters elements with stable_support >= 3
    -- S = [e1, e3]. has_shortcut e1 S is false because e4 is not in S.
    decide

  -- Step 2: Prove e1 ∈ Pi_BRQ T
  have h_in_T : e1 ∈ Pi_BRQ T := by
    -- T = [e1, e4]. has_shortcut e1 T is false because e3 is not in T.
    decide

  -- Step 3: Apply the implications
  have h_in_union := h_S_T h_in_S h_in_T

  -- Step 4: Show that e1 is actually NOT in Pi_BRQ (S ++ T)
  have h_not_in_union : e1 ∉ Pi_BRQ (S ++ T) := by
    -- S ++ T = [e1, e3, e1, e4].
    -- has_shortcut e1 (S ++ T) is true because both e3 and e4 are present.
    -- Thus stable_support e1 (S ++ T) = 0.
    -- So e1 is filtered out.
    decide

  -- Contradiction!
  contradiction

end PEL4
