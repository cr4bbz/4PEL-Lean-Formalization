import PEL4.TopologicalEvidenceStabilityBoundary

namespace PEL4

/-!
# Gate 7: topological fixed points and raw introspection

The preceding gates separate raw topological necessity from the stronger
local-constancy filtered knowledge operator.  Before asking whether the full
knowledge operation is idempotent, this gate isolates the weaker but exact
fixed-point statement supplied by topology itself.

Classically, closure is idempotent and preserves finite unions.  Together with
the already verified interior laws this makes the two-channel topological Box
fully S4-like:

```text
Box(Box(e)) = Box(e)
Box(e AND_FDE f) = Box(e) AND_FDE Box(f)
```

pointwise on both evidence coordinates.

Since generalized stable knowledge is the FDE conjunction of

1. a raw Box profile, and
2. the Box-fixed exact constancy guard,

it follows that stable knowledge is itself fixed by raw topological Box.
-/

/-- Pointwise union of two regions. -/
def regionUnion {W : Type} (A B : EvidenceRegion W) : EvidenceRegion W :=
  fun w => A w ∨ B w

/-- Classical closure is idempotent. -/
theorem closure_idempotent_at
    {W : Type} (s : InteriorSemantics W) (A : EvidenceRegion W) (w : W) :
    s.closure (s.closure A) w ↔ s.closure A w := by
  classical
  have hComplClosure :
      regionCompl (s.closure A) = s.interior (regionCompl A) := by
    funext u
    apply propext
    simp [regionCompl, InteriorSemantics.closure]
  change (¬ s.interior (regionCompl (s.closure A)) w) ↔
    ¬ s.interior (regionCompl A) w
  rw [hComplClosure]
  have hIdem := s.interior_idempotent (regionCompl A) w
  constructor
  · intro hNotNested hInt
    exact hNotNested (hIdem.2 hInt)
  · intro hNotInt hNested
    exact hNotInt (hIdem.1 hNested)

/-- Classical closure preserves binary unions. -/
theorem closure_union_at
    {W : Type} (s : InteriorSemantics W)
    (A B : EvidenceRegion W) (w : W) :
    s.closure (regionUnion A B) w ↔ s.closure A w ∨ s.closure B w := by
  classical
  have hComplUnion :
      regionCompl (regionUnion A B) =
        regionInter (regionCompl A) (regionCompl B) := by
    funext u
    apply propext
    simp [regionCompl, regionUnion, regionInter]
  change (¬ s.interior (regionCompl (regionUnion A B)) w) ↔
    (¬ s.interior (regionCompl A) w) ∨
      (¬ s.interior (regionCompl B) w)
  rw [hComplUnion, s.interior_intersection]
  constructor
  · intro hNotBoth
    by_cases hA : s.interior (regionCompl A) w
    · exact Or.inr (fun hB => hNotBoth ⟨hA, hB⟩)
    · exact Or.inl hA
  · intro hNot
    rintro ⟨hA, hB⟩
    cases hNot with
    | inl hNotA => exact hNotA hA
    | inr hNotB => exact hNotB hB

/-- Full pointwise idempotence of topological Box on both evidence coordinates. -/
theorem topBox_full_idempotent_at
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    ((topBox s (topBox s e)).pos w ↔ (topBox s e).pos w) ∧
      ((topBox s (topBox s e)).neg w ↔ (topBox s e).neg w) := by
  constructor
  · exact topBox_positive_idempotent_at s e w
  · change s.closure (s.closure e.neg) w ↔ s.closure e.neg w
    exact closure_idempotent_at s e.neg w

/-- Topological Box preserves FDE conjunction on both evidence coordinates. -/
theorem topBox_and_full_at
    {W : Type} (s : InteriorSemantics W)
    (e f : TopologicalEvidence W) (w : W) :
    ((topBox s (e.and f)).pos w ↔
        (topBox s e).pos w ∧ (topBox s f).pos w) ∧
      ((topBox s (e.and f)).neg w ↔
        (topBox s e).neg w ∨ (topBox s f).neg w) := by
  constructor
  · exact topBox_positive_and s e f w
  · change s.closure (regionUnion e.neg f.neg) w ↔
      s.closure e.neg w ∨ s.closure f.neg w
    exact closure_union_at s e.neg f.neg w

/-- A profile is locally fixed by raw topological Box when both evidence coordinates are fixed. -/
def TopBoxFixedAt {W : Type}
    (s : InteriorSemantics W) (e : TopologicalEvidence W) (w : W) : Prop :=
  ((topBox s e).pos w ↔ e.pos w) ∧
    ((topBox s e).neg w ↔ e.neg w)

/-- Every raw Box image is Box-fixed. -/
theorem topBox_image_fixed_at
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    TopBoxFixedAt s (topBox s e) w := by
  exact topBox_full_idempotent_at s e w

/-- The exact local-constancy guard is a Box-fixed profile. -/
theorem constancy_guard_box_fixed_at
    {W V : Type} (s : InteriorSemantics W)
    (value : W → V) (w : W) :
    TopBoxFixedAt s (topologicalConstancyGuard s value) w := by
  exact ⟨topBox_constancyGuard_positive_fixed s value w,
    topBox_constancyGuard_negative_fixed s value w⟩

/-- FDE conjunction of two Box-fixed profiles is again Box-fixed. -/
theorem topBox_and_fixed_of_fixed
    {W : Type} (s : InteriorSemantics W)
    (e f : TopologicalEvidence W) (w : W)
    (hE : TopBoxFixedAt s e w)
    (hF : TopBoxFixedAt s f w) :
    TopBoxFixedAt s (e.and f) w := by
  have hDist := topBox_and_full_at s e f w
  constructor
  · constructor
    · intro h
      have hPair := hDist.1.mp h
      exact ⟨hE.1.mp hPair.1, hF.1.mp hPair.2⟩
    · rintro ⟨he, hf⟩
      exact hDist.1.mpr ⟨hE.1.mpr he, hF.1.mpr hf⟩
  · constructor
    · intro h
      have hOr := hDist.2.mp h
      cases hOr with
      | inl he => exact Or.inl (hE.2.mp he)
      | inr hf => exact Or.inr (hF.2.mp hf)
    · intro h
      apply hDist.2.mpr
      cases h with
      | inl he => exact Or.inl (hE.2.mpr he)
      | inr hf => exact Or.inr (hF.2.mpr hf)

/--
Generalized stable knowledge is fixed by raw topological Box at every point.

This is the exact topological introspection statement available before defining
an iterated full `K`: `Box(K_stable(phi))` has precisely the same positive and
negative evidence as `K_stable(phi)`.
-/
theorem topologicalStableKnowledge_box_fixed_at
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W) :
    TopBoxFixedAt s (topologicalStableKnowledge s value) w := by
  unfold topologicalStableKnowledge
  apply topBox_and_fixed_of_fixed
  · exact topBox_image_fixed_at s (kripkeEvidence value) w
  · exact constancy_guard_box_fixed_at s value w

/-- Positive raw introspection of stable knowledge follows immediately. -/
theorem topologicalStableKnowledge_positive_raw_introspection
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W)
    (hK : (topologicalStableKnowledge s value).pos w) :
    (topBox s (topologicalStableKnowledge s value)).pos w := by
  exact (topologicalStableKnowledge_box_fixed_at s value w).1.mpr hK

/-- Negative evidence is also preserved exactly by one raw Box iteration. -/
theorem topologicalStableKnowledge_negative_raw_introspection
    {W : Type} (s : InteriorSemantics W)
    (value : W → FDEValue) (w : W) :
    (topBox s (topologicalStableKnowledge s value)).neg w ↔
      (topologicalStableKnowledge s value).neg w := by
  exact (topologicalStableKnowledge_box_fixed_at s value w).2

/-!
## Interpretation

Gate 7 yields a stronger geometric structure than the initial Gate 1 result.
Classically, the complete two-channel topological Box is idempotent, not merely
its positive coordinate, and it preserves FDE conjunction fully.

Consequently

```text
Box(K_stable(phi)) = K_stable(phi)
```

pointwise on positive and negative evidence.

This resembles positive introspection, but the distinction is important:

* `Box(K_stable(phi))` applies raw topological necessity to the already formed
  knowledge profile;
* `K_stable(K_stable(phi))` would recompute a new local-constancy guard for the
  knowledge profile itself.

The former is now a theorem.  The latter remains a separate research question.
That distinction is precisely where four-valued epistemic geometry may depart
from ordinary S4 introspection even though its raw modal shell is fully S4-like.
-/

end PEL4
