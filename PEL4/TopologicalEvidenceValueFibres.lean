import PEL4.TopologicalEvidenceStabilityBoundary

namespace PEL4

/-!
# Gate 9: topology of the four FDE value fibres

The preceding gates identified stable knowledge with local constancy of the
complete four-valued state.  This module decomposes that abstract condition into
the four concrete FDE phases themselves.

For a value profile `v : W → FDEValue`, write

```text
X_T = {w | v(w) = T}
X_F = {w | v(w) = F}
X_B = {w | v(w) = B}
X_N = {w | v(w) = N}.
```

Their interiors are the robust cores of the four phases.  Their boundaries are
the points where a phase is topologically adherent but not locally stable.
-/

/-- The fibre carrying a fixed FDE value. -/
def fdeValueRegion {W : Type}
    (value : W → FDEValue) (q : FDEValue) : EvidenceRegion W :=
  fun w => value w = q

/-- A point lies robustly inside phase `q`. -/
def FDEPhaseInteriorAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q : FDEValue) (w : W) : Prop :=
  s.interior (fdeValueRegion value q) w

/-- A point lies in the closure of phase `q`. -/
def FDEPhaseClosureAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q : FDEValue) (w : W) : Prop :=
  s.closure (fdeValueRegion value q) w

/-- The topological boundary of a fixed FDE phase. -/
def FDEPhaseBoundaryAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q : FDEValue) (w : W) : Prop :=
  FDEPhaseClosureAt s value q w ∧ ¬ FDEPhaseInteriorAt s value q w

/-- Two FDE phases are simultaneously adherent at a point. -/
def FDEPhaseContactAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q r : FDEValue) (w : W) : Prop :=
  FDEPhaseClosureAt s value q w ∧ FDEPhaseClosureAt s value r w

/-- The four FDE values exhaust every complete evidence state. -/
theorem fde_value_four_cases (v : FDEValue) :
    v = FDEValue.T ∨ v = FDEValue.F ∨
      v = FDEValue.B ∨ v = FDEValue.N := by
  cases v with
  | mk pos neg =>
      cases pos <;> cases neg <;>
        simp [FDEValue.T, FDEValue.F, FDEValue.B, FDEValue.N]

/-- Distinct FDE fibres cannot overlap pointwise. -/
theorem fdeValueRegion_disjoint_of_ne
    {W : Type} (value : W → FDEValue)
    {q r : FDEValue} (hqr : q ≠ r) (w : W) :
    ¬ (fdeValueRegion value q w ∧ fdeValueRegion value r w) := by
  intro h
  exact hqr (h.1.symm.trans h.2)

/-- A point in a phase interior really carries that FDE value. -/
theorem phase_interior_has_value
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    (q : FDEValue) (w : W)
    (hInt : FDEPhaseInteriorAt s value q w) :
    value w = q := by
  exact s.interior_subset (fdeValueRegion value q) w hInt

/-- The fibre through `w` is exactly the named FDE fibre of its current value. -/
theorem valueFiber_eq_current_fde_region
    {W : Type} (value : W → FDEValue) (w : W) :
    valueFiber value w = fdeValueRegion value (value w) := by
  rfl

/-- Local constancy is exactly membership in the interior of the current FDE phase. -/
theorem topological_local_constancy_iff_current_phase_interior
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W) :
    TopologicallyLocallyConstantAt s value w ↔
      FDEPhaseInteriorAt s value (value w) w := by
  rfl

/-- The union of the four robust FDE phase cores. -/
def fdePhaseInteriorUnion {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue) : EvidenceRegion W :=
  fun w =>
    FDEPhaseInteriorAt s value FDEValue.T w ∨
    FDEPhaseInteriorAt s value FDEValue.F w ∨
    FDEPhaseInteriorAt s value FDEValue.B w ∨
    FDEPhaseInteriorAt s value FDEValue.N w

/--
The central Gate 9 decomposition.

A complete FDE-valued profile is locally constant exactly at points belonging to
the robust interior of one of the four FDE phases.
-/
theorem topological_local_constancy_iff_four_phase_interior
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W) :
    TopologicallyLocallyConstantAt s value w ↔
      fdePhaseInteriorUnion s value w := by
  constructor
  · intro hLC
    have hCurrent : FDEPhaseInteriorAt s value (value w) w :=
      (topological_local_constancy_iff_current_phase_interior s value w).1 hLC
    rcases fde_value_four_cases (value w) with hT | hF | hB | hN
    · exact Or.inl (by simpa [hT] using hCurrent)
    · exact Or.inr (Or.inl (by simpa [hF] using hCurrent))
    · exact Or.inr (Or.inr (Or.inl (by simpa [hB] using hCurrent)))
    · exact Or.inr (Or.inr (Or.inr (by simpa [hN] using hCurrent)))
  · intro h
    rcases h with hT | hF | hB | hN
    · have hw : value w = FDEValue.T :=
        phase_interior_has_value s value FDEValue.T w hT
      have hCurrent : FDEPhaseInteriorAt s value (value w) w := by
        simpa [hw] using hT
      exact (topological_local_constancy_iff_current_phase_interior
        s value w).2 hCurrent
    · have hw : value w = FDEValue.F :=
        phase_interior_has_value s value FDEValue.F w hF
      have hCurrent : FDEPhaseInteriorAt s value (value w) w := by
        simpa [hw] using hF
      exact (topological_local_constancy_iff_current_phase_interior
        s value w).2 hCurrent
    · have hw : value w = FDEValue.B :=
        phase_interior_has_value s value FDEValue.B w hB
      have hCurrent : FDEPhaseInteriorAt s value (value w) w := by
        simpa [hw] using hB
      exact (topological_local_constancy_iff_current_phase_interior
        s value w).2 hCurrent
    · have hw : value w = FDEValue.N :=
        phase_interior_has_value s value FDEValue.N w hN
      have hCurrent : FDEPhaseInteriorAt s value (value w) w := by
        simpa [hw] using hN
      exact (topological_local_constancy_iff_current_phase_interior
        s value w).2 hCurrent

/-- Region-level form of the four-phase decomposition. -/
theorem topological_local_constancy_region_eq_phase_interiors
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue) :
    topologicalLocalConstancyRegion s value =
      fdePhaseInteriorUnion s value := by
  funext w
  apply propext
  exact topological_local_constancy_iff_four_phase_interior s value w

/-- A non-locally-constant point lies on the boundary of its own FDE phase. -/
theorem not_local_constancy_implies_own_phase_boundary
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W)
    (hNotLC : ¬ TopologicallyLocallyConstantAt s value w) :
    FDEPhaseBoundaryAt s value (value w) w := by
  constructor
  · exact closure_superset s (fdeValueRegion value (value w)) w rfl
  · intro hInt
    exact hNotLC
      ((topological_local_constancy_iff_current_phase_interior
        s value w).2 hInt)

/-- Local constancy is equivalently absence from the boundary of the current phase. -/
theorem local_constancy_iff_not_own_phase_boundary
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W) :
    TopologicallyLocallyConstantAt s value w ↔
      ¬ FDEPhaseBoundaryAt s value (value w) w := by
  constructor
  · intro hLC hBoundary
    exact hBoundary.2
      ((topological_local_constancy_iff_current_phase_interior
        s value w).1 hLC)
  · intro hNotBoundary
    classical
    by_cases hLC : TopologicallyLocallyConstantAt s value w
    · exact hLC
    · exact False.elim
        (hNotBoundary (not_local_constancy_implies_own_phase_boundary
          s value w hLC))

/-- Robust interiors of distinct FDE phases are disjoint. -/
theorem distinct_phase_interiors_disjoint
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {q r : FDEValue} (hqr : q ≠ r) (w : W)
    (hQ : FDEPhaseInteriorAt s value q w) :
    ¬ FDEPhaseInteriorAt s value r w := by
  intro hR
  have hqVal := phase_interior_has_value s value q w hQ
  have hrVal := phase_interior_has_value s value r w hR
  exact hqr (hqVal.symm.trans hrVal)

/--
A robust point of one phase is not even adherent to a distinct phase.

Thus phase interiors are stronger than pairwise disjointness: every robust FDE
core has an open buffer excluding the closures of all other value fibres.
-/
theorem phase_interior_excludes_other_phase_closure
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {q r : FDEValue} (hqr : q ≠ r) (w : W)
    (hQ : FDEPhaseInteriorAt s value q w) :
    ¬ FDEPhaseClosureAt s value r w := by
  intro hClosureR
  have hSubset :
      RegionSubset (fdeValueRegion value q)
        (regionCompl (fdeValueRegion value r)) := by
    intro u huq hur
    exact hqr (huq.symm.trans hur)
  have hInteriorComplR :
      s.interior (regionCompl (fdeValueRegion value r)) w :=
    s.interior_monotone hSubset w hQ
  exact hClosureR hInteriorComplR

/-- Contact between two distinct FDE phase closures can occur only outside the locally constant locus. -/
theorem distinct_phase_contact_implies_not_local_constancy
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {q r : FDEValue} (hqr : q ≠ r) (w : W)
    (hContact : FDEPhaseContactAt s value q r w) :
    ¬ TopologicallyLocallyConstantAt s value w := by
  intro hLC
  have hOwn : FDEPhaseInteriorAt s value (value w) w :=
    (topological_local_constancy_iff_current_phase_interior s value w).1 hLC
  by_cases hwq : value w = q
  · have hQ : FDEPhaseInteriorAt s value q w := by
      simpa [hwq] using hOwn
    exact (phase_interior_excludes_other_phase_closure
      s value hqr w hQ) hContact.2
  · have hRNe : value w ≠ r := by
      intro hwr
      have hCurrentClosureQ : FDEPhaseClosureAt s value q w := hContact.1
      exact (phase_interior_excludes_other_phase_closure
        s value hwq w hOwn) hCurrentClosureQ
    have hCurrentClosureR : FDEPhaseClosureAt s value r w := hContact.2
    exact (phase_interior_excludes_other_phase_closure
      s value hRNe w hOwn) hCurrentClosureR

/-!
## Minimal two-phase contact witness

The Gate 6 Sierpinski profile already realizes contact between the `T` and `F`
phase closures.  At the non-isolated focus the actual value is `T`, but the
isolated `F` point lies in every relevant closure neighbourhood.  Hence phase
contact coincides there with failure of local constancy.
-/

/-- The Sierpinski focus lies in the closure of both the T and F fibres. -/
theorem sierpinski_focus_T_F_phase_contact :
    FDEPhaseContactAt SierpinskiInteriorSemantics
      sierpinskiBoundaryValue FDEValue.T FDEValue.F
      SierpinskiPoint.focus := by
  constructor
  · exact closure_superset SierpinskiInteriorSemantics
      (fdeValueRegion sierpinskiBoundaryValue FDEValue.T)
      SierpinskiPoint.focus (by rfl)
  · rw [sierpinski_closure_focus_iff]
    exact Or.inr (by rfl)

/-- Consequently the Sierpinski focus is not locally constant by phase-contact geometry alone. -/
theorem sierpinski_focus_not_locally_constant_from_phase_contact :
    ¬ TopologicallyLocallyConstantAt SierpinskiInteriorSemantics
      sierpinskiBoundaryValue SierpinskiPoint.focus := by
  exact distinct_phase_contact_implies_not_local_constancy
    SierpinskiInteriorSemantics sierpinskiBoundaryValue
    (by native_decide) SierpinskiPoint.focus
    sierpinski_focus_T_F_phase_contact

/-!
## Interpretation

Gate 9 turns local constancy into a phase geometry:

```text
LC(v) = Int(X_T) ∪ Int(X_F) ∪ Int(X_B) ∪ Int(X_N).
```

Hence stable points are exactly the robust cores of the four complete FDE
states.  Every non-stable point lies on the boundary of its own current phase.
Moreover, the interior of one phase is separated from the closure of every
other phase, so contact between distinct phase closures is a sufficient witness
of epistemic instability.

This gives a paper-ready distinction unavailable in pointwise four-valued
semantics alone:

* `w ∈ Int(X_B)` is robust inconsistency;
* `w ∈ X_B \ Int(X_B)` is fragile inconsistency and lies on the `B` boundary;
* simultaneous adherence to distinct phase closures marks a genuine transition
  zone between complete information states.

The next natural gate is to classify which pairs and higher-order collections of
phase closures can meet, and whether the resulting contact pattern has a finite
combinatorial invariant such as a nerve or adjacency graph.
-/

end PEL4