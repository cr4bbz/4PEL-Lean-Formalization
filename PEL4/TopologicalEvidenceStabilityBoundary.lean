import PEL4.TopologicalEvidenceLocalConstancy

namespace PEL4

/-!
# Gate 6: the boundary of epistemic stability

Gate 5 showed that the local-constancy locus

```text
LC(v) = {w | v is locally constant at w}
```

is open in every `InteriorSemantics`.  This makes its topological boundary a
natural epistemic object.

There are now three qualitatively different regions:

1. `LC(v)`: exact local stability;
2. `Cl(LC(v)) \ LC(v)`: exact stability fails, but stable points are
   topologically adherent to the current point;
3. `Int(complement LC(v))`: instability itself is locally robust.

The second region is the new phase.  It supports a precise notion of fragile or
approximate stability: stability is false at the point, but topologically
possible in every-neighbourhood sense.
-/

/-- A point lies on the stability boundary when it is adherent to, but not in, the local-constancy locus. -/
def TopologicalStabilityBoundaryAt {W V : Type}
    (s : InteriorSemantics W) (value : W → V) (w : W) : Prop :=
  s.closure (topologicalLocalConstancyRegion s value) w ∧
    ¬ topologicalLocalConstancyRegion s value w

/-- Instability is robust when the point lies in the interior of the non-constant region. -/
def TopologicallyRobustlyUnstableAt {W V : Type}
    (s : InteriorSemantics W) (value : W → V) (w : W) : Prop :=
  s.interior (regionCompl (topologicalLocalConstancyRegion s value)) w

/-- Possibility applied to the exact constancy guard gives an approximate-stability guard. -/
def topologicalApproximateConstancyGuard {W V : Type}
    (s : InteriorSemantics W) (value : W → V) : TopologicalEvidence W :=
  topDiamond s (topologicalConstancyGuard s value)

/-- Exact stability makes the exact constancy guard strict true. -/
theorem exact_constancy_guard_true_of_local_constancy
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hLC : TopologicallyLocallyConstantAt s value w) :
    TopologicalStrictTrueAt (topologicalConstancyGuard s value) w := by
  constructor
  · exact hLC
  · intro hNotLC
    exact hNotLC hLC

/-- Exact stability also makes approximate stability strict true. -/
theorem approximate_constancy_guard_true_of_local_constancy
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hLC : TopologicallyLocallyConstantAt s value w) :
    TopologicalStrictTrueAt (topologicalApproximateConstancyGuard s value) w := by
  constructor
  · exact closure_superset s (topologicalLocalConstancyRegion s value) w hLC
  · intro hInteriorNotLC
    have hNotLC : ¬ topologicalLocalConstancyRegion s value w :=
      s.interior_subset
        (regionCompl (topologicalLocalConstancyRegion s value))
        w hInteriorNotLC
    exact hNotLC hLC

/-- Boundary points are exact failures of local constancy. -/
theorem exact_constancy_guard_false_on_boundary
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hBoundary : TopologicalStabilityBoundaryAt s value w) :
    TopologicalStrictFalseAt (topologicalConstancyGuard s value) w := by
  exact ⟨hBoundary.2, hBoundary.2⟩

/--
At a stability boundary point, approximate stability is strict true.

The positive coordinate is closure-membership of `LC(v)`.  The negative
coordinate is interior-membership of its complement.  These cannot coexist by
the definition of closure, so a boundary point has exact guard `F` but
approximate guard `T`.
-/
theorem approximate_constancy_guard_true_on_boundary
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hBoundary : TopologicalStabilityBoundaryAt s value w) :
    TopologicalStrictTrueAt (topologicalApproximateConstancyGuard s value) w := by
  constructor
  · exact hBoundary.1
  · intro hInteriorNotLC
    exact hBoundary.1 hInteriorNotLC

/-- Robust instability makes both exact and approximate stability strict false. -/
theorem approximate_constancy_guard_false_of_robust_instability
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hUnstable : TopologicallyRobustlyUnstableAt s value w) :
    TopologicalStrictFalseAt (topologicalApproximateConstancyGuard s value) w := by
  constructor
  · intro hClosure
    exact hClosure hUnstable
  · exact hUnstable

/-- Robust instability also excludes exact local constancy. -/
theorem robust_instability_implies_not_local_constancy
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hUnstable : TopologicallyRobustlyUnstableAt s value w) :
    ¬ TopologicallyLocallyConstantAt s value w := by
  intro hLC
  have hNotLC : ¬ topologicalLocalConstancyRegion s value w :=
    s.interior_subset
      (regionCompl (topologicalLocalConstancyRegion s value)) w hUnstable
  exact hNotLC hLC

/--
Every point belongs to exactly one of the three qualitative phases up to the
explicit disjunction: locally constant, stability boundary, or robustly
unstable.
-/
theorem topological_stability_three_phase_cover
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W) :
    TopologicallyLocallyConstantAt s value w ∨
      TopologicalStabilityBoundaryAt s value w ∨
      TopologicallyRobustlyUnstableAt s value w := by
  classical
  by_cases hLC : TopologicallyLocallyConstantAt s value w
  · exact Or.inl hLC
  · by_cases hClosure : s.closure (topologicalLocalConstancyRegion s value) w
    · exact Or.inr (Or.inl ⟨hClosure, hLC⟩)
    · have hDoubleNegInterior :
          ¬ ¬ s.interior
            (regionCompl (topologicalLocalConstancyRegion s value)) w := by
        exact hClosure
      have hInterior :
          s.interior
            (regionCompl (topologicalLocalConstancyRegion s value)) w :=
        Classical.byContradiction hDoubleNegInterior
      exact Or.inr (Or.inr hInterior)

/-- The stability boundary and robust-instability interior are disjoint. -/
theorem stability_boundary_not_robustly_unstable
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W)
    (hBoundary : TopologicalStabilityBoundaryAt s value w) :
    ¬ TopologicallyRobustlyUnstableAt s value w := by
  intro hUnstable
  exact hBoundary.1 hUnstable

/-!
## Approximate stable knowledge

Replace the exact local-constancy guard by its topological possibility.  This
operator agrees with raw topological Box throughout the exact-stable region and
also on the stability boundary, but still collapses in robustly unstable
regions.
-/

/-- Knowledge filtered by approximate rather than exact local constancy. -/
def topologicalApproximateKnowledge {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue) : TopologicalEvidence W :=
  (topBox s (kripkeEvidence value)).and
    (topologicalApproximateConstancyGuard s value)

/-- On the stability boundary, approximate knowledge reduces to ordinary topological Box. -/
theorem topologicalApproximateKnowledge_of_boundary
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue) (w : W)
    (hBoundary : TopologicalStabilityBoundaryAt s value w) :
    ((topologicalApproximateKnowledge s value).pos w ↔
        (topBox s (kripkeEvidence value)).pos w) ∧
      ((topologicalApproximateKnowledge s value).neg w ↔
        (topBox s (kripkeEvidence value)).neg w) := by
  have hApproxT := approximate_constancy_guard_true_on_boundary s value w hBoundary
  constructor
  · change ((topBox s (kripkeEvidence value)).pos w ∧
        (topologicalApproximateConstancyGuard s value).pos w) ↔
      (topBox s (kripkeEvidence value)).pos w
    exact and_iff_left hApproxT.1
  · change ((topBox s (kripkeEvidence value)).neg w ∨
        (topologicalApproximateConstancyGuard s value).neg w) ↔
      (topBox s (kripkeEvidence value)).neg w
    constructor
    · intro h
      cases h with
      | inl hBox => exact hBox
      | inr hApproxNeg => exact False.elim (hApproxT.2 hApproxNeg)
    · intro hBox
      exact Or.inl hBox

/-- On robustly unstable points, approximate knowledge is strict false. -/
theorem topologicalApproximateKnowledge_false_of_robust_instability
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue) (w : W)
    (hUnstable : TopologicallyRobustlyUnstableAt s value w) :
    TopologicalStrictFalseAt (topologicalApproximateKnowledge s value) w := by
  have hApproxF :=
    approximate_constancy_guard_false_of_robust_instability s value w hUnstable
  constructor
  · intro hPos
    exact hApproxF.1 hPos.2
  · exact Or.inr hApproxF.2

/-!
## Minimal Sierpinski boundary witness

The two-point Sierpinski topology already realizes the new phase.  Give the
isolated `neighbour` and non-isolated `focus` different FDE values.  The value
map is locally constant at the isolated point, not locally constant at the
focus, while the isolated point lies in every relevant closure at the focus.
Thus `focus` is a genuine stability-boundary point.
-/

/-- A nonconstant two-point FDE profile for the boundary witness. -/
def sierpinskiBoundaryValue : SierpinskiPoint → FDEValue
  | SierpinskiPoint.focus => FDEValue.T
  | SierpinskiPoint.neighbour => FDEValue.F

/-- The isolated Sierpinski point is locally constant. -/
theorem sierpinski_boundary_neighbour_locally_constant :
    TopologicallyLocallyConstantAt SierpinskiInteriorSemantics
      sierpinskiBoundaryValue SierpinskiPoint.neighbour := by
  native_decide

/-- The non-isolated focus is not locally constant for the split profile. -/
theorem sierpinski_boundary_focus_not_locally_constant :
    ¬ TopologicallyLocallyConstantAt SierpinskiInteriorSemantics
      sierpinskiBoundaryValue SierpinskiPoint.focus := by
  native_decide

/-- The focus is nevertheless in the closure of the local-constancy locus. -/
theorem sierpinski_boundary_focus_in_constancy_closure :
    SierpinskiInteriorSemantics.closure
      (topologicalLocalConstancyRegion SierpinskiInteriorSemantics
        sierpinskiBoundaryValue)
      SierpinskiPoint.focus := by
  rw [sierpinski_closure_focus_iff]
  exact Or.inr sierpinski_boundary_neighbour_locally_constant

/-- The focus realizes the exact stability boundary. -/
theorem sierpinski_focus_is_stability_boundary :
    TopologicalStabilityBoundaryAt SierpinskiInteriorSemantics
      sierpinskiBoundaryValue SierpinskiPoint.focus := by
  exact ⟨sierpinski_boundary_focus_in_constancy_closure,
    sierpinski_boundary_focus_not_locally_constant⟩

/-- At the Sierpinski focus, exact constancy is `F` while approximate constancy is `T`. -/
theorem sierpinski_boundary_exact_false_approximate_true :
    TopologicalStrictFalseAt
        (topologicalConstancyGuard SierpinskiInteriorSemantics
          sierpinskiBoundaryValue) SierpinskiPoint.focus ∧
      TopologicalStrictTrueAt
        (topologicalApproximateConstancyGuard SierpinskiInteriorSemantics
          sierpinskiBoundaryValue) SierpinskiPoint.focus := by
  exact ⟨
    exact_constancy_guard_false_on_boundary SierpinskiInteriorSemantics
      sierpinskiBoundaryValue SierpinskiPoint.focus
      sierpinski_focus_is_stability_boundary,
    approximate_constancy_guard_true_on_boundary SierpinskiInteriorSemantics
      sierpinskiBoundaryValue SierpinskiPoint.focus
      sierpinski_focus_is_stability_boundary⟩

/-!
## Interpretation

Gate 6 exposes a phase that ordinary Kripke successor lists hide naturally.
For the local-constancy locus `LC(v)`:

```text
stable interior:      exact guard = T, approximate guard = T
stability boundary:   exact guard = F, approximate guard = T
robust instability:   exact guard = F, approximate guard = F
```

The boundary therefore distinguishes two kinds of failure of stable knowledge.
At a boundary point, exact epistemic stability fails but is arbitrarily locally
recoverable in the topological sense.  In the interior of the unstable region,
even that approximate recovery fails.

This suggests a new four-valued epistemic vocabulary even though the guard
itself remains crisp: ordinary topological Box measures robustness of truth and
falsity evidence, exact local constancy measures stable knowledge, and closure
of local constancy measures *fragile recoverability*.

A natural next gate is to study iteration and fixed points.  Since both raw Box
and the exact constancy guard are topologically stable objects, generalized
stable knowledge may itself be a Box-fixed point.  If so, positive
introspection would emerge geometrically rather than as an additional epistemic
axiom.
-/

end PEL4
