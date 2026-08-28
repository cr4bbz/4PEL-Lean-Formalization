import PEL4.TopologicalEvidenceStability

namespace PEL4

/-!
# Gate 5: local constancy beyond Alexandrov spaces

Gate 4 identified the repository's accessible-value stability predicate with
constancy on the minimal Alexandrov neighbourhood `R(w)`.  A general topological
space need not have a smallest neighbourhood, so that formulation cannot be the
final geometric notion.

The interior operator itself already supplies the right replacement.  For a
value profile `v : W → V`, define the fibre through `w`

```text
F_w = {u | v(u) = v(w)}.
```

Then `v` is locally constant at `w` exactly when `w` lies in the interior of
its own fibre:

```text
LC(v,w)  iff  w ∈ Int(F_w).
```

This formulation requires no privileged neighbourhood and works for every
`InteriorSemantics` in the repository.
-/

/-- The fibre of a value profile through a point. -/
def valueFiber {W V : Type} (value : W → V) (w : W) : EvidenceRegion W :=
  fun u => value u = value w

/-- Genuine topological local constancy, expressed purely through interior. -/
def TopologicallyLocallyConstantAt {W V : Type}
    (s : InteriorSemantics W) (value : W → V) (w : W) : Prop :=
  s.interior (valueFiber value w) w

/-- The locus on which a value profile is locally constant. -/
def topologicalLocalConstancyRegion {W V : Type}
    (s : InteriorSemantics W) (value : W → V) : EvidenceRegion W :=
  fun w => TopologicallyLocallyConstantAt s value w

/-- Equal values determine equal fibres. -/
theorem valueFiber_eq_of_value_eq
    {W V : Type} (value : W → V) {u w : W}
    (h : value u = value w) :
    valueFiber value u = valueFiber value w := by
  funext x
  apply propext
  constructor
  · intro hx
    exact hx.trans h
  · intro hx
    exact hx.trans h.symm

/--
The local-constancy locus is open: applying interior to it changes nothing.

This is a genuine topological theorem rather than an Alexandrov artefact.  If
`v` is constant on some open neighbourhood of `w`, then every point of that
neighbourhood has the same value and is itself locally constant.
-/
theorem topological_local_constancy_region_interior_fixed
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W) :
    s.interior (topologicalLocalConstancyRegion s value) w ↔
      topologicalLocalConstancyRegion s value w := by
  constructor
  · intro h
    exact s.interior_subset (topologicalLocalConstancyRegion s value) w h
  · intro hLC
    have hNested : s.interior (s.interior (valueFiber value w)) w :=
      (s.interior_idempotent (valueFiber value w) w).2 hLC
    have hSubset :
        RegionSubset (s.interior (valueFiber value w))
          (topologicalLocalConstancyRegion s value) := by
      intro u hu
      have hValue : value u = value w :=
        s.interior_subset (valueFiber value w) u hu
      have hFiber : valueFiber value u = valueFiber value w :=
        valueFiber_eq_of_value_eq value hValue
      change s.interior (valueFiber value u) u
      rw [hFiber]
      exact hu
    exact s.interior_monotone hSubset w hNested

/-- A crisp topological evidence guard for local constancy. -/
def topologicalConstancyGuard {W V : Type}
    (s : InteriorSemantics W) (value : W → V) : TopologicalEvidence W :=
  { pos := topologicalLocalConstancyRegion s value
  , neg := regionCompl (topologicalLocalConstancyRegion s value) }

/-- The positive constancy guard is itself Box-stable. -/
theorem topBox_constancyGuard_positive_fixed
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W) :
    (topBox s (topologicalConstancyGuard s value)).pos w ↔
      (topologicalConstancyGuard s value).pos w := by
  exact topological_local_constancy_region_interior_fixed s value w

/--
The negative constancy guard is Box-stable as well: the complement of the open
local-constancy locus is closed.
-/
theorem topBox_constancyGuard_negative_fixed
    {W V : Type} (s : InteriorSemantics W) (value : W → V) (w : W) :
    (topBox s (topologicalConstancyGuard s value)).neg w ↔
      (topologicalConstancyGuard s value).neg w := by
  classical
  change (¬ s.interior
      (regionCompl (regionCompl (topologicalLocalConstancyRegion s value))) w) ↔
    ¬ topologicalLocalConstancyRegion s value w
  have hDoubleCompl :
      regionCompl (regionCompl (topologicalLocalConstancyRegion s value)) =
        topologicalLocalConstancyRegion s value := by
    funext u
    apply propext
    simp [regionCompl]
  rw [hDoubleCompl]
  have hOpen := topological_local_constancy_region_interior_fixed s value w
  constructor
  · intro hNotInt hLC
    exact hNotInt (hOpen.2 hLC)
  · intro hNotLC hInt
    exact hNotLC (hOpen.1 hInt)

/-!
## General topological stable knowledge

For a complete FDE-valued profile, combine coordinatewise topological Box with
the crisp local-constancy guard using the ordinary FDE conjunction already
encoded by `TopologicalEvidence.and`.
-/

/-- Stable knowledge on an arbitrary interior space. -/
def topologicalStableKnowledge {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue) : TopologicalEvidence W :=
  (topBox s (kripkeEvidence value)).and
    (topologicalConstancyGuard s value)

/-- At a locally constant point, stable knowledge reduces locally to topological Box. -/
theorem topologicalStableKnowledge_of_local_constancy
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue) (w : W)
    (hLC : TopologicallyLocallyConstantAt s value w) :
    ((topologicalStableKnowledge s value).pos w ↔
        (topBox s (kripkeEvidence value)).pos w) ∧
      ((topologicalStableKnowledge s value).neg w ↔
        (topBox s (kripkeEvidence value)).neg w) := by
  constructor
  · change ((topBox s (kripkeEvidence value)).pos w ∧
        topologicalLocalConstancyRegion s value w) ↔
      (topBox s (kripkeEvidence value)).pos w
    exact and_iff_left hLC
  · change ((topBox s (kripkeEvidence value)).neg w ∨
        ¬ topologicalLocalConstancyRegion s value w) ↔
      (topBox s (kripkeEvidence value)).neg w
    constructor
    · intro h
      cases h with
      | inl hBox => exact hBox
      | inr hNot => exact False.elim (hNot hLC)
    · intro hBox
      exact Or.inl hBox

/-- Failure of genuine local constancy forces generalized stable knowledge to strict falsity. -/
theorem topologicalStableKnowledge_false_of_not_local_constancy
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue) (w : W)
    (hNotLC : ¬ TopologicallyLocallyConstantAt s value w) :
    TopologicalStrictFalseAt (topologicalStableKnowledge s value) w := by
  constructor
  · intro hPos
    exact hNotLC hPos.2
  · exact Or.inr hNotLC

/-!
## Recovery of the Alexandrov gate

On a reflexive/transitive successor frame, the abstract definition above must
collapse back to Gate 4.  Reflexivity is the key: pairwise constancy over
`R(w)` is equivalent to every successor having the same value as `w` itself.
-/

/-- General topological local constancy equals successor-neighbourhood constancy on Alexandrov S4 frames. -/
theorem alexandrov_local_constancy_iff_successor_local_constancy
    {W V : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → V) (w : W) :
    TopologicallyLocallyConstantAt
        (successorInteriorSemantics R hRefl hTrans) value w ↔
      SuccessorLocallyConstantAt R value w := by
  change (∀ u, u ∈ R w → value u = value w) ↔
    (∀ u, u ∈ R w → ∀ v, v ∈ R w → value u = value v)
  constructor
  · intro h u hu v hv
    exact (h u hu).trans (h v hv).symm
  · intro h u hu
    exact h u hu w (hRefl w)

/-- Gate 4's Boolean stability test is exactly genuine topological local constancy on the Alexandrov space. -/
theorem accessible_stability_iff_alexandrov_local_constancy
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hRefl : SuccessorReflexive (m.R i))
    (hTrans : SuccessorTransitive (m.R i))
    (w : W) (phi : Formula Atom Ag) :
    accessibleFDEValueStable m i w phi = true ↔
      TopologicallyLocallyConstantAt
        (successorInteriorSemantics (m.R i) hRefl hTrans)
        (fun u => eval m u phi) w := by
  rw [accessible_stability_iff_successor_local_constancy]
  exact (alexandrov_local_constancy_iff_successor_local_constancy
    (m.R i) hRefl hTrans (fun u => eval m u phi) w).symm

/-!
## Interpretation

Gate 5 removes the special Alexandrov crutch.

Local constancy is not fundamentally "same value on the successor list".  Its
coordinate-free form is

```text
w ∈ Int({u | value(u) = value(w)}).
```

Three consequences now hold for every algebraic interior semantics in the
repository:

1. the local-constancy locus is open;
2. the crisp constancy guard is itself fixed by topological Box;
3. generalized stable knowledge is ordinary topological Box on locally constant
   points and strict false off that locus.

The Alexandrov construction from Gates 3–4 is recovered as a theorem, not kept
as a definition.  This is important conceptually: the evidence-stability clause
of 4PEL has a genuine topological reading even where no smallest neighbourhood
exists.

The next question is no longer whether the local-constancy interpretation
survives general topology.  It does.  The sharper question is what its boundary
looks like: can the closure of the locally constant region support a meaningful
four-valued notion of *approximately stable knowledge* at points where exact
knowledge fails?
-/

end PEL4
