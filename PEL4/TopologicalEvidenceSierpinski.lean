import PEL4.TopologicalEvidence

namespace PEL4

/-!
# Sierpinski witness for topological 4PEL

This module gives the first concrete finite topology for the abstract semantics
in `PEL4.TopologicalEvidence`.

The two-point Sierpinski space is enough to make every local boundary effect
visible. At the distinguished `focus` point, interior requires a proposition
to hold both at `focus` and at its neighbouring point, while closure requires
it to hold at at least one of them.

The resulting observation is particularly useful for 4PEL:

```text
Box at focus     = FDE conjunction of the two point-values
Diamond at focus = FDE disjunction of the two point-values
```

The equality here is semantic: the positive and negative evidence propositions
at the focus point are equivalent to the two Boolean coordinates of the
corresponding FDE value. This avoids adding a computability assumption to the
abstract topological semantics merely to package propositions back into Bools.
-/

/-- The two points of the Sierpinski witness. -/
inductive SierpinskiPoint where
  | focus
  | neighbour
deriving DecidableEq, Repr

/--
Interior for the topology with open sets
`∅`, `{neighbour}`, and `{focus, neighbour}`.
-/
def sierpinskiInterior
    (A : EvidenceRegion SierpinskiPoint) : EvidenceRegion SierpinskiPoint
  | SierpinskiPoint.focus =>
      A SierpinskiPoint.focus ∧ A SierpinskiPoint.neighbour
  | SierpinskiPoint.neighbour =>
      A SierpinskiPoint.neighbour

/-- The concrete Sierpinski interior satisfies the abstract topological laws. -/
def SierpinskiInteriorSemantics : InteriorSemantics SierpinskiPoint :=
  { interior := sierpinskiInterior
  , interior_subset := by
      intro A w h
      cases w with
      | focus => exact h.1
      | neighbour => exact h
  , interior_monotone := by
      intro A B hAB w h
      cases w with
      | focus =>
          exact ⟨hAB SierpinskiPoint.focus h.1,
            hAB SierpinskiPoint.neighbour h.2⟩
      | neighbour =>
          exact hAB SierpinskiPoint.neighbour h
  , interior_idempotent := by
      intro A w
      cases w with
      | focus =>
          constructor
          · intro h
            exact h.1
          · intro h
            exact ⟨h, h.2⟩
      | neighbour =>
          rfl
  , interior_top := by
      intro w
      cases w with
      | focus => exact ⟨True.intro, True.intro⟩
      | neighbour => exact True.intro
  , interior_intersection := by
      intro A B w
      cases w with
      | focus =>
          constructor
          · rintro ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩⟩
            exact ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩
          · rintro ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩
            exact ⟨⟨ha0, hb0⟩, ⟨ha1, hb1⟩⟩
      | neighbour =>
          rfl
  }

/-- At the focus point, Sierpinski interior is conjunction across both points. -/
theorem sierpinski_interior_focus_iff
    (A : EvidenceRegion SierpinskiPoint) :
    SierpinskiInteriorSemantics.interior A SierpinskiPoint.focus ↔
      A SierpinskiPoint.focus ∧ A SierpinskiPoint.neighbour := by
  rfl

/-- At the focus point, Sierpinski closure is disjunction across both points. -/
theorem sierpinski_closure_focus_iff
    (A : EvidenceRegion SierpinskiPoint) :
    SierpinskiInteriorSemantics.closure A SierpinskiPoint.focus ↔
      A SierpinskiPoint.focus ∨ A SierpinskiPoint.neighbour := by
  classical
  change ¬ (¬ A SierpinskiPoint.focus ∧ ¬ A SierpinskiPoint.neighbour) ↔
    A SierpinskiPoint.focus ∨ A SierpinskiPoint.neighbour
  constructor
  · intro h
    by_cases h0 : A SierpinskiPoint.focus
    · exact Or.inl h0
    · by_cases h1 : A SierpinskiPoint.neighbour
      · exact Or.inr h1
      · exact False.elim (h ⟨h0, h1⟩)
  · intro h hNot
    cases h with
    | inl h0 => exact hNot.1 h0
    | inr h1 => exact hNot.2 h1

/-- At the neighbour point, Sierpinski closure reduces to ordinary truth there. -/
theorem sierpinski_closure_neighbour_iff
    (A : EvidenceRegion SierpinskiPoint) :
    SierpinskiInteriorSemantics.closure A SierpinskiPoint.neighbour ↔
      A SierpinskiPoint.neighbour := by
  classical
  change ¬ ¬ A SierpinskiPoint.neighbour ↔ A SierpinskiPoint.neighbour
  constructor
  · intro h
    by_cases ha : A SierpinskiPoint.neighbour
    · exact ha
    · exact False.elim (h ha)
  · intro ha hNot
    exact hNot ha

/--
Embed two ordinary FDE values as the positive/negative evidence profiles of the
two Sierpinski points.
-/
def sierpinskiEvidence
    (source neighbour : FDEValue) : TopologicalEvidence SierpinskiPoint :=
  { pos := fun w =>
      match w with
      | SierpinskiPoint.focus => source.pos = true
      | SierpinskiPoint.neighbour => neighbour.pos = true
  , neg := fun w =>
      match w with
      | SierpinskiPoint.focus => source.neg = true
      | SierpinskiPoint.neighbour => neighbour.neg = true
  }

/--
A topological evidence profile semantically represents an FDE value at one
point when its two evidence propositions agree with the value's two Boolean
coordinates.
-/
def TopologicalEvidenceRepresentsAt {W : Type}
    (e : TopologicalEvidence W) (w : W) (v : FDEValue) : Prop :=
  (e.pos w ↔ v.pos = true) ∧ (e.neg w ↔ v.neg = true)

/-- The positive Box coordinate at `focus` is the positive coordinate of FDE conjunction. -/
theorem sierpinski_topBox_focus_pos_iff_fde_and
    (source neighbour : FDEValue) :
    (topBox SierpinskiInteriorSemantics
        (sierpinskiEvidence source neighbour)).pos SierpinskiPoint.focus ↔
      (FDEValue.and source neighbour).pos = true := by
  change (source.pos = true ∧ neighbour.pos = true) ↔
    (source.pos && neighbour.pos) = true
  cases source.pos <;> cases neighbour.pos <;> simp

/-- The negative Box coordinate at `focus` is the negative coordinate of FDE conjunction. -/
theorem sierpinski_topBox_focus_neg_iff_fde_and
    (source neighbour : FDEValue) :
    (topBox SierpinskiInteriorSemantics
        (sierpinskiEvidence source neighbour)).neg SierpinskiPoint.focus ↔
      (FDEValue.and source neighbour).neg = true := by
  change SierpinskiInteriorSemantics.closure
      (sierpinskiEvidence source neighbour).neg SierpinskiPoint.focus ↔
    (source.neg || neighbour.neg) = true
  rw [sierpinski_closure_focus_iff]
  change (source.neg = true ∨ neighbour.neg = true) ↔
    (source.neg || neighbour.neg) = true
  cases source.neg <;> cases neighbour.neg <;> simp

/--
At the focus point, topological Box semantically reconstructs FDE conjunction
of the source value with the neighbouring value.
-/
theorem sierpinski_topBox_focus_represents_fde_and
    (source neighbour : FDEValue) :
    TopologicalEvidenceRepresentsAt
      (topBox SierpinskiInteriorSemantics (sierpinskiEvidence source neighbour))
      SierpinskiPoint.focus (FDEValue.and source neighbour) := by
  exact ⟨sierpinski_topBox_focus_pos_iff_fde_and source neighbour,
    sierpinski_topBox_focus_neg_iff_fde_and source neighbour⟩

/-- The positive Diamond coordinate at `focus` is the positive coordinate of FDE disjunction. -/
theorem sierpinski_topDiamond_focus_pos_iff_fde_or
    (source neighbour : FDEValue) :
    (topDiamond SierpinskiInteriorSemantics
        (sierpinskiEvidence source neighbour)).pos SierpinskiPoint.focus ↔
      (FDEValue.or source neighbour).pos = true := by
  change SierpinskiInteriorSemantics.closure
      (sierpinskiEvidence source neighbour).pos SierpinskiPoint.focus ↔
    (source.pos || neighbour.pos) = true
  rw [sierpinski_closure_focus_iff]
  change (source.pos = true ∨ neighbour.pos = true) ↔
    (source.pos || neighbour.pos) = true
  cases source.pos <;> cases neighbour.pos <;> simp

/-- The negative Diamond coordinate at `focus` is the negative coordinate of FDE disjunction. -/
theorem sierpinski_topDiamond_focus_neg_iff_fde_or
    (source neighbour : FDEValue) :
    (topDiamond SierpinskiInteriorSemantics
        (sierpinskiEvidence source neighbour)).neg SierpinskiPoint.focus ↔
      (FDEValue.or source neighbour).neg = true := by
  change (source.neg = true ∧ neighbour.neg = true) ↔
    (source.neg && neighbour.neg) = true
  cases source.neg <;> cases neighbour.neg <;> simp

/--
At the focus point, topological Diamond semantically reconstructs FDE
disjunction of the source value with the neighbouring value.
-/
theorem sierpinski_topDiamond_focus_represents_fde_or
    (source neighbour : FDEValue) :
    TopologicalEvidenceRepresentsAt
      (topDiamond SierpinskiInteriorSemantics (sierpinskiEvidence source neighbour))
      SierpinskiPoint.focus (FDEValue.or source neighbour) := by
  exact ⟨sierpinski_topDiamond_focus_pos_iff_fde_or source neighbour,
    sierpinski_topDiamond_focus_neg_iff_fde_or source neighbour⟩

/-- `T` is the identity for the Sierpinski Box witness, so every FDE target is reachable. -/
theorem sierpinski_topBox_T_source_reaches_any
    (target : FDEValue) :
    TopologicalEvidenceRepresentsAt
      (topBox SierpinskiInteriorSemantics (sierpinskiEvidence FDEValue.T target))
      SierpinskiPoint.focus target := by
  rcases target with ⟨p, n⟩
  cases p <;> cases n <;>
    simpa [FDEValue.T, FDEValue.and] using
      (sierpinski_topBox_focus_represents_fde_and
        FDEValue.T ({ pos := p, neg := n } : FDEValue))

/-- `F` is the identity for the Sierpinski Diamond witness, so every FDE target is reachable. -/
theorem sierpinski_topDiamond_F_source_reaches_any
    (target : FDEValue) :
    TopologicalEvidenceRepresentsAt
      (topDiamond SierpinskiInteriorSemantics (sierpinskiEvidence FDEValue.F target))
      SierpinskiPoint.focus target := by
  rcases target with ⟨p, n⟩
  cases p <;> cases n <;>
    simpa [FDEValue.F, FDEValue.or] using
      (sierpinski_topDiamond_focus_represents_fde_or
        FDEValue.F ({ pos := p, neg := n } : FDEValue))

/-!
## Consequence for the transition landscape

Gate 1 proved the universal restrictions

```text
Box:     F -> F       B -> {B, F}       N -> {N, F}
Diamond: T -> T       B -> {B, T}       N -> {N, T}
```

The two identity theorems above settle the two previously unclassified source
rows sharply:

```text
Box:     T -> {T, F, B, N}
Diamond: F -> {T, F, B, N}
```

Moreover, the same two-point space supplies witnesses for both alternatives in
each restricted row simply by choosing the neighbouring FDE value. Hence the
coordinate restrictions from Gate 1 are not artifacts of an impoverished model;
they are the exact local transition bounds for the candidate semantics.

A useful structural reading emerges:

* necessity moves downward in positive support and upward in negative support;
* possibility moves upward in positive support and downward in negative support;
* the Sierpinski boundary realizes those movements as the familiar FDE meet and
  join operations.

The next gate should compare this topological modality with the repository's
existing Kripke `know`/`poss` semantics and isolate a representation theorem or
a precise obstruction.
-/

end PEL4
