import PEL4.FDE

namespace PEL4

/-!
# Topological evidence semantics for 4PEL

This module starts an experimental topological semantics for the two evidence
coordinates of 4PEL.

The central idea is to interpret positive and negative evidence as regions of a
state space.  An interior operator then expresses local stability.  Closure is
defined dually through complement.

For an evidence profile `e = (P, N)` we study the modal pair

```text
Box e     = (Int P, Cl N)
Diamond e = (Cl P, Int N)
```

This is deliberately algebraic rather than a full point-set-topology
formalization.  The repository remains dependency-free, while the laws used by
the modal interpretation are made explicit and machine-checkable.
-/

/-- A region of states. -/
abbrev EvidenceRegion (W : Type) := W → Prop

/-- Pointwise inclusion between regions. -/
def RegionSubset {W : Type} (A B : EvidenceRegion W) : Prop :=
  ∀ w, A w → B w

/-- The complement of a region. -/
def regionCompl {W : Type} (A : EvidenceRegion W) : EvidenceRegion W :=
  fun w => ¬ A w

/-- The intersection of two regions. -/
def regionInter {W : Type} (A B : EvidenceRegion W) : EvidenceRegion W :=
  fun w => A w ∧ B w

/--
An algebraic interior semantics.

The fields isolate exactly the topological laws needed by the first research
gate: deflationarity, monotonicity, idempotence, preservation of the whole
space, and preservation of binary intersections.
-/
structure InteriorSemantics (W : Type) where
  interior : EvidenceRegion W → EvidenceRegion W
  interior_subset :
    ∀ (A : EvidenceRegion W), RegionSubset (interior A) A
  interior_monotone :
    ∀ {A B : EvidenceRegion W},
      RegionSubset A B → RegionSubset (interior A) (interior B)
  interior_idempotent :
    ∀ (A : EvidenceRegion W) (w : W),
      interior (interior A) w ↔ interior A w
  interior_top :
    ∀ w : W, interior (fun _ => True) w
  interior_intersection :
    ∀ (A B : EvidenceRegion W) (w : W),
      interior (regionInter A B) w ↔ interior A w ∧ interior B w

/-- Topological closure, defined as the complement of the interior of the complement. -/
def InteriorSemantics.closure {W : Type}
    (s : InteriorSemantics W) (A : EvidenceRegion W) : EvidenceRegion W :=
  fun w => ¬ s.interior (regionCompl A) w

/-- Every region is contained in its closure. -/
theorem closure_superset
    {W : Type} (s : InteriorSemantics W) (A : EvidenceRegion W) :
    RegionSubset A (s.closure A) := by
  intro w hA hInteriorCompl
  exact (s.interior_subset (regionCompl A) w hInteriorCompl) hA

/-- Closure is monotone. -/
theorem closure_monotone
    {W : Type} (s : InteriorSemantics W)
    {A B : EvidenceRegion W}
    (hAB : RegionSubset A B) :
    RegionSubset (s.closure A) (s.closure B) := by
  intro w hClosureA hInteriorComplB
  apply hClosureA
  have hCompl : RegionSubset (regionCompl B) (regionCompl A) := by
    intro u hNotB hA
    exact hNotB (hAB u hA)
  exact s.interior_monotone hCompl w hInteriorComplB

/-- A proposition carries independent positive and negative evidence regions. -/
structure TopologicalEvidence (W : Type) where
  pos : EvidenceRegion W
  neg : EvidenceRegion W

/-- Strong FDE negation swaps positive and negative evidence. -/
def TopologicalEvidence.not {W : Type}
    (e : TopologicalEvidence W) : TopologicalEvidence W :=
  { pos := e.neg, neg := e.pos }

/-- FDE-style conjunction on evidence regions. -/
def TopologicalEvidence.and {W : Type}
    (e f : TopologicalEvidence W) : TopologicalEvidence W :=
  { pos := regionInter e.pos f.pos
  , neg := fun w => e.neg w ∨ f.neg w }

/-- Topological necessity: stable positive evidence and approximable negative evidence. -/
def topBox {W : Type}
    (s : InteriorSemantics W) (e : TopologicalEvidence W) :
    TopologicalEvidence W :=
  { pos := s.interior e.pos
  , neg := s.closure e.neg }

/-- Topological possibility: approximable positive evidence and stable negative evidence. -/
def topDiamond {W : Type}
    (s : InteriorSemantics W) (e : TopologicalEvidence W) :
    TopologicalEvidence W :=
  { pos := s.closure e.pos
  , neg := s.interior e.neg }

/-- Local strict truth (`T`) in the evidence-pair representation. -/
def TopologicalStrictTrueAt {W : Type}
    (e : TopologicalEvidence W) (w : W) : Prop :=
  e.pos w ∧ ¬ e.neg w

/-- Local strict falsity (`F`) in the evidence-pair representation. -/
def TopologicalStrictFalseAt {W : Type}
    (e : TopologicalEvidence W) (w : W) : Prop :=
  ¬ e.pos w ∧ e.neg w

/-- Local glut (`B`) in the evidence-pair representation. -/
def TopologicalBothAt {W : Type}
    (e : TopologicalEvidence W) (w : W) : Prop :=
  e.pos w ∧ e.neg w

/-- Local gap (`N`) in the evidence-pair representation. -/
def TopologicalNeitherAt {W : Type}
    (e : TopologicalEvidence W) (w : W) : Prop :=
  ¬ e.pos w ∧ ¬ e.neg w

/-- At decidable points, a topological evidence profile projects back to the core FDE value. -/
def TopologicalEvidence.valueAt {W : Type}
    (e : TopologicalEvidence W) (w : W)
    [Decidable (e.pos w)] [Decidable (e.neg w)] : FDEValue :=
  { pos := decide (e.pos w)
  , neg := decide (e.neg w) }

/-!
## Duality

Because strong FDE negation swaps the two evidence coordinates, the proposed
Box/Diamond pair is exactly dual by construction.
-/

/-- Strong negation of Box is Diamond of strong negation. -/
theorem topological_not_box_eq_diamond_not
    {W : Type} (s : InteriorSemantics W) (e : TopologicalEvidence W) :
    (topBox s e).not = topDiamond s e.not := by
  rfl

/-- Strong negation of Diamond is Box of strong negation. -/
theorem topological_not_diamond_eq_box_not
    {W : Type} (s : InteriorSemantics W) (e : TopologicalEvidence W) :
    (topDiamond s e).not = topBox s e.not := by
  rfl

/-!
## Positive S4 profile

The positive coordinate of Box is an interior operator.  Hence factivity and
positive introspection arise directly from the algebraic topology rather than
from a Kripke-frame condition.
-/

/-- Positive topological necessity is factive (`T`). -/
theorem topBox_positive_factive
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    (topBox s e).pos w → e.pos w := by
  intro h
  exact s.interior_subset e.pos w h

/-- The positive coordinate of Box is pointwise idempotent (`4`, and its converse). -/
theorem topBox_positive_idempotent_at
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    (topBox s (topBox s e)).pos w ↔ (topBox s e).pos w := by
  change s.interior (s.interior e.pos) w ↔ s.interior e.pos w
  exact s.interior_idempotent e.pos w

/-- Positive Box preserves conjunction exactly. -/
theorem topBox_positive_and
    {W : Type} (s : InteriorSemantics W)
    (e f : TopologicalEvidence W) (w : W) :
    (topBox s (e.and f)).pos w ↔
      (topBox s e).pos w ∧ (topBox s f).pos w := by
  change s.interior (regionInter e.pos f.pos) w ↔
    s.interior e.pos w ∧ s.interior f.pos w
  exact s.interior_intersection e.pos f.pos w

/-!
## Coordinate monotonicity

The asymmetry of the candidate semantics is already visible locally:

* Box can remove positive support, but cannot remove negative support already
  present at the point.
* Diamond can add positive support, but cannot add negative support at a point
  where negative support was absent.
-/

/-- Existing negative evidence survives Box because the negative coordinate uses closure. -/
theorem topBox_negative_extensive
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    e.neg w → (topBox s e).neg w := by
  intro h
  exact closure_superset s e.neg w h

/-- Existing positive evidence survives Diamond because the positive coordinate uses closure. -/
theorem topDiamond_positive_extensive
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    e.pos w → (topDiamond s e).pos w := by
  intro h
  exact closure_superset s e.pos w h

/-- Negative evidence under Diamond is factive because that coordinate uses interior. -/
theorem topDiamond_negative_factive
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W) :
    (topDiamond s e).neg w → e.neg w := by
  intro h
  exact s.interior_subset e.neg w h

/-!
## First local FDE transition theorems

These results are the first genuinely four-valued consequence of the
semantics.  They are stronger than the usual one-coordinate S4 observations.
-/

/-- A locally strict-false state is fixed by Box. -/
theorem topBox_strictFalse_fixed
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W)
    (hF : TopologicalStrictFalseAt e w) :
    TopologicalStrictFalseAt (topBox s e) w := by
  constructor
  · intro hBoxPos
    exact hF.1 (topBox_positive_factive s e w hBoxPos)
  · exact topBox_negative_extensive s e w hF.2

/-- A locally strict-true state is fixed by Diamond. -/
theorem topDiamond_strictTrue_fixed
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W)
    (hT : TopologicalStrictTrueAt e w) :
    TopologicalStrictTrueAt (topDiamond s e) w := by
  constructor
  · exact topDiamond_positive_extensive s e w hT.1
  · intro hDiamondNeg
    exact hT.2 (topDiamond_negative_factive s e w hDiamondNeg)

/-- A glut under Box can only remain a glut or collapse to strict falsity. -/
theorem topBox_both_transition
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W)
    (hB : TopologicalBothAt e w) :
    TopologicalBothAt (topBox s e) w ∨
      TopologicalStrictFalseAt (topBox s e) w := by
  classical
  have hNeg : (topBox s e).neg w :=
    topBox_negative_extensive s e w hB.2
  by_cases hPos : (topBox s e).pos w
  · exact Or.inl ⟨hPos, hNeg⟩
  · exact Or.inr ⟨hPos, hNeg⟩

/-- Dually, a glut under Diamond can only remain a glut or collapse to strict truth. -/
theorem topDiamond_both_transition
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W)
    (hB : TopologicalBothAt e w) :
    TopologicalBothAt (topDiamond s e) w ∨
      TopologicalStrictTrueAt (topDiamond s e) w := by
  classical
  have hPos : (topDiamond s e).pos w :=
    topDiamond_positive_extensive s e w hB.1
  by_cases hNeg : (topDiamond s e).neg w
  · exact Or.inl ⟨hPos, hNeg⟩
  · exact Or.inr ⟨hPos, hNeg⟩

/-- A gap under Box can only remain a gap or become strict falsity. -/
theorem topBox_neither_transition
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W)
    (hN : TopologicalNeitherAt e w) :
    TopologicalNeitherAt (topBox s e) w ∨
      TopologicalStrictFalseAt (topBox s e) w := by
  classical
  have hNotPos : ¬ (topBox s e).pos w := by
    intro hBoxPos
    exact hN.1 (topBox_positive_factive s e w hBoxPos)
  by_cases hNeg : (topBox s e).neg w
  · exact Or.inr ⟨hNotPos, hNeg⟩
  · exact Or.inl ⟨hNotPos, hNeg⟩

/-- Dually, a gap under Diamond can only remain a gap or become strict truth. -/
theorem topDiamond_neither_transition
    {W : Type} (s : InteriorSemantics W)
    (e : TopologicalEvidence W) (w : W)
    (hN : TopologicalNeitherAt e w) :
    TopologicalNeitherAt (topDiamond s e) w ∨
      TopologicalStrictTrueAt (topDiamond s e) w := by
  classical
  have hNotNeg : ¬ (topDiamond s e).neg w := by
    intro hDiamondNeg
    exact hN.2 (topDiamond_negative_factive s e w hDiamondNeg)
  by_cases hPos : (topDiamond s e).pos w
  · exact Or.inr ⟨hPos, hNotNeg⟩
  · exact Or.inl ⟨hPos, hNotNeg⟩

/-!
## Interpretation

At the first gate, the topological semantics therefore yields the local
transition constraints

```text
Box:     F -> F       B -> {B, F}       N -> {N, F}
Diamond: T -> T       B -> {B, T}       N -> {N, T}
```

The missing source cases are intentionally not classified yet.  For example,
a strict-true point can acquire negative support under Box when negative
evidence is arbitrarily close, while its positive support can simultaneously
lose stability.  This is exactly the boundary behaviour that should be studied
next with concrete finite topologies.

The main next questions are:

1. Which full four-valued modal laws follow from these coordinate laws?
2. Which transition sets are sharp, i.e. all listed outcomes realizable?
3. How do discrete, indiscrete, and Sierpinski-style finite topologies differ?
4. Can the resulting modality be related cleanly to the existing
   evidence-stable Kripke knowledge operator in `PEL4.ModalLanguage`?
-/

end PEL4
