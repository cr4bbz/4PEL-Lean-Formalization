import PEL4.TopologicalEvidencePhaseNerve
import PEL4.TopologicalEvidenceKripke

namespace PEL4

/-!
# Gate 11: Alexandrov classification of the four-phase nerve

Gate 10 defined the closure-contact nerve of the four FDE value fibres in an
arbitrary interior semantics.  On a successor Alexandrov space, closure has an
exact relational reading: a point lies in the closure of phase `q` precisely
when one of its successors carries `q`.

This file packages that observation at the level of arbitrary phase families.
The complete phase nerve is the downward closure of the phase profiles realized
in successor neighbourhoods.  The edge, triangle, and tetrahedron notions from
Gate 10 are recovered as low-dimensional corollaries.
-/

/-- Phase `q` occurs in the successor neighbourhood of `w`. -/
def ReachableFDEPhase {W : Type} [DecidableEq W]
    (R : W → FiniteSet W) (value : W → FDEValue)
    (w : W) (q : FDEValue) : Prop :=
  ∃ u, u ∈ R w ∧ value u = q

/-- A family of phases has a common closure witness at `w`. -/
def FDEPhaseSimplexAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (phases : FDEValue → Prop) (w : W) : Prop :=
  ∀ q, phases q → FDEPhaseClosureAt s value q w

/-- A family of phases is a simplex of the global closure-contact nerve. -/
def FDEPhaseSimplex {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (phases : FDEValue → Prop) : Prop :=
  ∃ w, FDEPhaseSimplexAt s value phases w

/-- In a successor Alexandrov space, phase closure is exactly phase reachability. -/
theorem alexandrov_phase_closure_iff_reachable_phase
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → FDEValue) (w : W) (q : FDEValue) :
    FDEPhaseClosureAt (successorInteriorSemantics R hRefl hTrans)
        value q w ↔
      ReachableFDEPhase R value w q := by
  rw [show FDEPhaseClosureAt (successorInteriorSemantics R hRefl hTrans)
      value q w =
      (successorInteriorSemantics R hRefl hTrans).closure
        (fdeValueRegion value q) w by rfl]
  rw [successor_closure_iff_exists R hRefl hTrans]
  rfl

/-- Local classification: a phase family meets at `w` iff all its phases occur among successors. -/
theorem alexandrov_phase_simplex_at_iff
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → FDEValue) (phases : FDEValue → Prop) (w : W) :
    FDEPhaseSimplexAt (successorInteriorSemantics R hRefl hTrans)
        value phases w ↔
      ∀ q, phases q → ReachableFDEPhase R value w q := by
  constructor
  · intro h q hq
    exact (alexandrov_phase_closure_iff_reachable_phase
      R hRefl hTrans value w q).1 (h q hq)
  · intro h q hq
    exact (alexandrov_phase_closure_iff_reachable_phase
      R hRefl hTrans value w q).2 (h q hq)

/-- Global classification of every simplex in the Alexandrov phase nerve. -/
theorem alexandrov_phase_simplex_iff
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → FDEValue) (phases : FDEValue → Prop) :
    FDEPhaseSimplex (successorInteriorSemantics R hRefl hTrans)
        value phases ↔
      ∃ w, ∀ q, phases q → ReachableFDEPhase R value w q := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (alexandrov_phase_simplex_at_iff
      R hRefl hTrans value phases w).1 hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨w, (alexandrov_phase_simplex_at_iff
      R hRefl hTrans value phases w).2 hw⟩

/-- The phase nerve is downward closed under inclusion of phase families. -/
theorem fde_phase_nerve_downward_closed
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {small large : FDEValue → Prop}
    (hSub : ∀ q, small q → large q)
    (hLarge : FDEPhaseSimplex s value large) :
    FDEPhaseSimplex s value small := by
  rcases hLarge with ⟨w, hw⟩
  exact ⟨w, fun q hq => hw q (hSub q hq)⟩

/-- Gate 10 edges are exactly pairs co-realized in one successor profile. -/
theorem alexandrov_phase_adjacent_iff
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → FDEValue) (q r : FDEValue) :
    FDEPhaseAdjacent (successorInteriorSemantics R hRefl hTrans)
        value q r ↔
      q ≠ r ∧ ∃ w,
        ReachableFDEPhase R value w q ∧
        ReachableFDEPhase R value w r := by
  constructor
  · rintro ⟨hqr, w, hq, hr⟩
    exact ⟨hqr, w,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w q).1 hq,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w r).1 hr⟩
  · rintro ⟨hqr, w, hq, hr⟩
    exact ⟨hqr, w,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w q).2 hq,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w r).2 hr⟩

/-- Gate 10 triangles are exactly triples co-realized in one successor profile. -/
theorem alexandrov_phase_triangle_iff
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → FDEValue) (q r t : FDEValue) :
    FDEPhaseTriangle (successorInteriorSemantics R hRefl hTrans)
        value q r t ↔
      q ≠ r ∧ q ≠ t ∧ r ≠ t ∧ ∃ w,
        ReachableFDEPhase R value w q ∧
        ReachableFDEPhase R value w r ∧
        ReachableFDEPhase R value w t := by
  constructor
  · rintro ⟨hqr, hqt, hrt, w, hq, hr, ht⟩
    exact ⟨hqr, hqt, hrt, w,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w q).1 hq,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w r).1 hr,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w t).1 ht⟩
  · rintro ⟨hqr, hqt, hrt, w, hq, hr, ht⟩
    exact ⟨hqr, hqt, hrt, w,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w q).2 hq,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w r).2 hr,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w t).2 ht⟩

/-- Gate 10 tetrahedra are exactly successor profiles containing all four phases. -/
theorem alexandrov_phase_tetrahedron_iff
    {W : Type} [DecidableEq W]
    (R : W → FiniteSet W)
    (hRefl : SuccessorReflexive R)
    (hTrans : SuccessorTransitive R)
    (value : W → FDEValue) :
    FDEPhaseTetrahedron (successorInteriorSemantics R hRefl hTrans) value ↔
      ∃ w,
        ReachableFDEPhase R value w FDEValue.T ∧
        ReachableFDEPhase R value w FDEValue.F ∧
        ReachableFDEPhase R value w FDEValue.B ∧
        ReachableFDEPhase R value w FDEValue.N := by
  constructor
  · rintro ⟨w, hT, hF, hB, hN⟩
    exact ⟨w,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.T).1 hT,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.F).1 hF,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.B).1 hB,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.N).1 hN⟩
  · rintro ⟨w, hT, hF, hB, hN⟩
    exact ⟨w,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.T).2 hT,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.F).2 hF,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.B).2 hB,
      (alexandrov_phase_closure_iff_reachable_phase
        R hRefl hTrans value w FDEValue.N).2 hN⟩

/-!
## Pairwise completeness does not fill higher simplices

The following small S4 model has one two-point accessibility component for
each ordered pair of phases.  Hence every distinct pair occurs together in
some successor profile, while no profile contains more than two phases.
-/

/-- Worlds are ordered pairs of FDE phases. -/
abbrev PairPhaseWorld := FDEValue × FDEValue

/-- Each world sees itself and the world with its two coordinates exchanged. -/
def pairPhaseR (w : PairPhaseWorld) : FiniteSet PairPhaseWorld :=
  [w, (w.2, w.1)]

/-- A pair world carries its first coordinate as its actual phase. -/
def pairPhaseValue (w : PairPhaseWorld) : FDEValue :=
  w.1

theorem pairPhaseR_reflexive : SuccessorReflexive pairPhaseR := by
  intro w
  simp [pairPhaseR]

theorem pairPhaseR_transitive : SuccessorTransitive pairPhaseR := by
  intro w u hu v hv
  simp [pairPhaseR] at hu hv ⊢
  rcases hu with rfl | rfl <;> simp_all

/-- Reachability in the pair model means equality with one of the two coordinates. -/
theorem pairPhase_reachable_iff (w : PairPhaseWorld) (q : FDEValue) :
    ReachableFDEPhase pairPhaseR pairPhaseValue w q ↔
      w.1 = q ∨ w.2 = q := by
  simp [ReachableFDEPhase, pairPhaseR, pairPhaseValue]

/-- Every two distinct phases are adjacent in the pair model. -/
theorem pairPhase_complete_contact_graph
    (q r : FDEValue) (hqr : q ≠ r) :
    FDEPhaseAdjacent
      (successorInteriorSemantics pairPhaseR
        pairPhaseR_reflexive pairPhaseR_transitive)
      pairPhaseValue q r := by
  rw [alexandrov_phase_adjacent_iff pairPhaseR
    pairPhaseR_reflexive pairPhaseR_transitive]
  refine ⟨hqr, (q, r), ?_, ?_⟩
  · exact (pairPhase_reachable_iff (q, r) q).2 (Or.inl rfl)
  · exact (pairPhase_reachable_iff (q, r) r).2 (Or.inr rfl)

/-- Despite its complete one-skeleton, the pair model has no four-phase simplex. -/
theorem pairPhase_no_tetrahedron :
    ¬ FDEPhaseTetrahedron
      (successorInteriorSemantics pairPhaseR
        pairPhaseR_reflexive pairPhaseR_transitive)
      pairPhaseValue := by
  rw [alexandrov_phase_tetrahedron_iff pairPhaseR
    pairPhaseR_reflexive pairPhaseR_transitive]
  rintro ⟨w, hT, hF, hB, _hN⟩
  rw [pairPhase_reachable_iff] at hT hF hB
  rcases hT with hT | hT <;>
    rcases hF with hF | hF <;>
    rcases hB with hB | hB <;>
    simp_all [FDEValue.T, FDEValue.F, FDEValue.B]

/-!
## Interpretation

For every world `w`, let `ReachPhases(w)` be the set of FDE values occurring
among its successors.  The Alexandrov phase nerve is exactly

```text
{ phases | exists w, phases ⊆ ReachPhases(w) }.
```

Thus it is the downward closure of the family of realized successor profiles.
Pairwise completeness of the contact graph does not imply a filled triangle or
tetrahedron: different edges may have different witness worlds.  Any stronger
restriction on the nerve must therefore arise from constraints on accessibility
or on the admissible value profiles, not from Alexandrov topology alone.
-/

end PEL4
