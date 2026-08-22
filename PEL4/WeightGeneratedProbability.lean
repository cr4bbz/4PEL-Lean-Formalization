import PEL4.FiniteProbabilityIntegrity
import Init.Data.Rat.Lemmas

namespace PEL4

/-!
# Weight-generated finite probability measures

`FiniteProbabilityIntegrity` introduced the stronger probability contract needed
before model-valued interpolation can be claimed.  This module gives a
constructive source of measures satisfying that contract.

For a duplicate-free finite support `R` and rational world weights `q`, define

```text
mu_q(S) = sum over x in R of (if x in S then q(x) else 0).
```

The iteration is over the canonical support rather than over the event list.
Consequently event order and duplicate presentation cannot change the mass.
If all support weights are nonnegative and the total support mass is one, the
generated measure satisfies finite probability integrity.
-/

/-- Event mass generated from rational point weights on a finite support.
The support, not the event list, controls the iteration. -/
def weightedEventMass {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat)
    (event : FiniteSet W) : Rat :=
  match support with
  | [] => 0
  | x :: xs =>
      (if x ∈ event then weight x else 0) +
        weightedEventMass xs weight event

/-- The legacy `ProbMeasure` induced by finite point weights. -/
def weightGeneratedMeasure {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat) : ProbMeasure W :=
  fun event => weightedEventMass support weight event

/-- Empty events have zero generated mass. -/
theorem weightedEventMass_empty
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat) :
    weightedEventMass support weight [] = 0 := by
  induction support with
  | nil => rfl
  | cons x xs ih =>
      simp [weightedEventMass, ih, Rat.zero_add, Rat.add_zero]

/-- Generated mass depends only on event membership, not list presentation. -/
theorem weightedEventMass_extensional
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat)
    (A B : FiniteSet W)
    (hExt : FiniteEventExtEq A B) :
    weightedEventMass support weight A =
      weightedEventMass support weight B := by
  induction support with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ∈ A ↔ x ∈ B := hExt x
      by_cases hA : x ∈ A
      · have hB : x ∈ B := hx.mp hA
        simp [weightedEventMass, hA, hB, ih]
      · have hB : x ∉ B := by
          intro hBin
          exact hA (hx.mpr hBin)
        simp [weightedEventMass, hA, hB, ih]

/-- Nonnegative support weights generate nonnegative event masses. -/
theorem weightedEventMass_nonnegative
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat)
    (event : FiniteSet W)
    (hWeight : ∀ x, x ∈ support → 0 ≤ weight x) :
    0 ≤ weightedEventMass support weight event := by
  induction support with
  | nil =>
      exact Rat.le_refl
  | cons x xs ih =>
      have hx : 0 ≤ weight x := hWeight x (by simp)
      have hxs : ∀ y, y ∈ xs → 0 ≤ weight y := by
        intro y hy
        exact hWeight y (by simp [hy])
      have hTail : 0 ≤ weightedEventMass xs weight event := ih hxs
      by_cases hMem : x ∈ event
      · simpa [weightedEventMass, hMem] using Rat.add_nonneg hx hTail
      · simpa [weightedEventMass, hMem, Rat.zero_add] using hTail

/-- Event inclusion is monotone for nonnegative generated measures. -/
theorem weightedEventMass_monotone
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat)
    (A B : FiniteSet W)
    (hSub : FiniteEventSubset A B)
    (hWeight : ∀ x, x ∈ support → 0 ≤ weight x) :
    weightedEventMass support weight A ≤
      weightedEventMass support weight B := by
  induction support with
  | nil =>
      exact Rat.le_refl
  | cons x xs ih =>
      have hx : 0 ≤ weight x := hWeight x (by simp)
      have hxs : ∀ y, y ∈ xs → 0 ≤ weight y := by
        intro y hy
        exact hWeight y (by simp [hy])
      have hTail :
          weightedEventMass xs weight A ≤
            weightedEventMass xs weight B :=
        ih hxs
      by_cases hA : x ∈ A
      · have hB : x ∈ B := hSub x hA
        have hAdd :=
          (Rat.add_le_add_left
            (a := weightedEventMass xs weight A)
            (b := weightedEventMass xs weight B)
            (c := weight x)).2 hTail
        simpa [weightedEventMass, hA, hB] using hAdd
      · by_cases hB : x ∈ B
        · have hRight :
              weightedEventMass xs weight B ≤
                weight x + weightedEventMass xs weight B := by
            have hAdd :=
              (Rat.add_le_add_right
                (a := 0) (b := weight x)
                (c := weightedEventMass xs weight B)).2 hx
            simpa [Rat.zero_add] using hAdd
          have hStep :
              weightedEventMass xs weight A ≤
                weight x + weightedEventMass xs weight B :=
            Rat.le_trans hTail hRight
          simpa [weightedEventMass, hA, hB, Rat.zero_add] using hStep
        · simpa [weightedEventMass, hA, hB, Rat.zero_add] using hTail

/-- Generated mass is finitely additive on disjoint event lists. -/
theorem weightedEventMass_add_disjoint
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat)
    (A B : FiniteSet W)
    (hDis : FiniteEventDisjoint A B) :
    weightedEventMass support weight (A ++ B) =
      weightedEventMass support weight A +
        weightedEventMass support weight B := by
  induction support with
  | nil =>
      simp [weightedEventMass, Rat.zero_add, Rat.add_zero]
  | cons x xs ih =>
      by_cases hA : x ∈ A
      · have hB : x ∉ B := by
          intro hBin
          exact hDis x hA hBin
        simp [weightedEventMass, hA, hB, ih,
          Rat.zero_add, Rat.add_zero, Rat.add_assoc]
      · by_cases hB : x ∈ B
        · simp [weightedEventMass, hA, hB, ih,
            Rat.zero_add, Rat.add_zero,
            Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]
        · simp [weightedEventMass, hA, hB, ih,
            Rat.zero_add, Rat.add_zero]

/-- A normalized nonnegative rational weight vector on a duplicate-free support. -/
structure FiniteWeightDistribution
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat) : Prop where
  support_nodup : support.Nodup
  nonnegative : ∀ x, x ∈ support → 0 ≤ weight x
  total : weightedEventMass support weight support = 1

/-- Every finite weight distribution generates a measure satisfying the full
finite probability integrity contract. -/
theorem weightGeneratedMeasure_integrity
    {W : Type} [DecidableEq W]
    (support : FiniteSet W) (weight : W → Rat)
    (hDist : FiniteWeightDistribution support weight) :
    FiniteProbabilityIntegrity
      (weightGeneratedMeasure support weight) support := by
  refine
    { support_nodup := hDist.support_nodup
      nonnegative := ?_
      extensional := ?_
      monotone := ?_
      add_disjoint := ?_
      empty := ?_
      total := ?_ }
  · intro S _ _
    exact weightedEventMass_nonnegative support weight S hDist.nonnegative
  · intro A B _ _ _ _ hExt
    exact weightedEventMass_extensional support weight A B hExt
  · intro A B _ _ hSub _
    exact weightedEventMass_monotone support weight A B hSub hDist.nonnegative
  · intro A B _ _ _ _ hDis
    exact weightedEventMass_add_disjoint support weight A B hDis
  · exact weightedEventMass_empty support weight
  · exact hDist.total

/-!
## Research consequence

This gate turns the stronger probability layer from a list of semantic axioms
into a reusable constructor.  Once a concrete model is described by a
nonnegative normalized weight vector on each accessibility support, its local
measure inherits `FiniteProbabilityIntegrity` generically.

The next gate will study convex rational interpolation of two distributions on
the same support.  If convex interpolation preserves `FiniteWeightDistribution`,
then the probability simplex becomes an explicit model-level path space rather
than only an interpretive picture.
-/

end PEL4
