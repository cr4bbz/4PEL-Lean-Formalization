import PEL4.NeighbourhoodBelief
import PEL4.Dynamics

namespace PEL4

/-!
# Graded aggregation: what replaces C below certainty

Lockean neighbourhoods are not closed under intersection (`neighbourhood_not_C`).
Under finite probability integrity the loss is exactly quantified: two neighbourhoods
at threshold `c` intersect in an event of mass at least `2c − 1`.  Since `c > 1/2`,
the intersection is never empty-massed (a strengthening of D), and at `c = 1` the
bound gives back aggregation.  This is the semantic content of the schema

  `B_c φ ∧ B_c ψ → B_{2c−1}(φ ∧ ψ)`,

a sound principle of the threshold logic beyond M, N, P, D.  Completeness of any
finite axiom system for a fixed `c ∈ (1/2, 1)` is not claimed.
-/

/-- **Graded aggregation**: `μ(A ∩ B) ≥ μ(A) + μ(B) − 1`. -/
theorem mass_intersection_lower_bound
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (A B : FiniteSet W) (hA : A.Nodup) (hB : B.Nodup)
    (hA' : FiniteEventSubset A (m.R i w)) (hB' : FiniteEventSubset B (m.R i w)) :
    m.mu i w (intersectWorlds A B) ≥ m.mu i w A + m.mu i w B - 1 := by
  let I := intersectWorlds A B
  let D := A.filter (fun u => !B.contains u)
  have hI : I.Nodup := hA.filter _
  have hD : D.Nodup := hA.filter _
  have hIs : FiniteEventSubset I (m.R i w) := fun x hx => hA' x (List.mem_filter.mp hx).1
  have hDs : FiniteEventSubset D (m.R i w) := fun x hx => hA' x (List.mem_filter.mp hx).1
  have hID : FiniteEventDisjoint I D := by
    intro x hx hx'
    have h1 := (List.mem_filter.mp hx).2
    have h2 := (List.mem_filter.mp hx').2
    simp at h1 h2
    exact h2 h1
  have hBD : FiniteEventDisjoint B D := by
    intro x hx hx'
    have h2 := (List.mem_filter.mp hx').2
    simp [hx] at h2
  have hnd1 : (I ++ D).Nodup := by
    rw [List.nodup_append]
    exact ⟨hI, hD, fun a ha b hb hab => hID a ha (hab ▸ hb)⟩
  have hnd2 : (B ++ D).Nodup := by
    rw [List.nodup_append]
    exact ⟨hB, hD, fun a ha b hb hab => hBD a ha (hab ▸ hb)⟩
  have hs1 : FiniteEventSubset (I ++ D) (m.R i w) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hIs x hx
    · exact hDs x hx
  have hs2 : FiniteEventSubset (B ++ D) (m.R i w) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hB' x hx
    · exact hDs x hx
  have hext : FiniteEventExtEq (I ++ D) A := by
    intro x
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (List.mem_filter.mp hx).1
      · exact (List.mem_filter.mp hx).1
    · intro hx
      apply List.mem_append.mpr
      by_cases hb : x ∈ B
      · exact Or.inl (List.mem_filter.mpr ⟨hx, by simpa using hb⟩)
      · exact Or.inr (List.mem_filter.mpr ⟨hx, by simpa using hb⟩)
  have e1 := (h i w).extensional (I ++ D) A hnd1 hA hs1 hA' hext
  have a1 := (h i w).add_disjoint I D hI hD hIs hDs hID
  have a2 := (h i w).add_disjoint B D hB hD hB' hDs hBD
  have mono := (h i w).monotone (B ++ D) (m.R i w) hnd2 (h i w).support_nodup hs2
    (fun x hx => hx)
  have tot := (h i w).total
  show m.mu i w I ≥ m.mu i w A + m.mu i w B - 1
  grind

/-- Two Lockean neighbourhoods meet in mass at least `2c − 1`. -/
theorem neighbourhood_graded_C
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (A B : FiniteSet W) (hA : A.Nodup) (hB : B.Nodup)
    (hA' : FiniteEventSubset A (m.R i w)) (hB' : FiniteEventSubset B (m.R i w))
    (hNA : BeliefNeighbourhood m i w A) (hNB : BeliefNeighbourhood m i w B) :
    m.mu i w (intersectWorlds A B) ≥ 2 * m.c i - 1 := by
  have hb := mass_intersection_lower_bound m h i w A B hA hB hA' hB'
  unfold BeliefNeighbourhood ThresholdNeighbourhood at hNA hNB
  grind

/-- In particular the intersection of two neighbourhoods has positive mass. -/
theorem neighbourhood_intersection_pos
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (h : ModelProbabilityIntegrity m) (i : Ag) (w : W)
    (A B : FiniteSet W) (hA : A.Nodup) (hB : B.Nodup)
    (hA' : FiniteEventSubset A (m.R i w)) (hB' : FiniteEventSubset B (m.R i w))
    (hNA : BeliefNeighbourhood m i w A) (hNB : BeliefNeighbourhood m i w B) :
    0 < m.mu i w (intersectWorlds A B) := by
  have hb := neighbourhood_graded_C m h i w A B hA hB hA' hB' hNA hNB
  have hc := m.c_gt_half i
  grind

end PEL4
