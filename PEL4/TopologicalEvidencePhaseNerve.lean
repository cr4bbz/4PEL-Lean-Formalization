import PEL4.TopologicalEvidenceValueFibres

namespace PEL4

/-!
# Gate 10: the closure-contact nerve of the four FDE phases

Gate 9 decomposed the locally constant locus into the robust interiors of the
four value fibres `X_T`, `X_F`, `X_B`, and `X_N`.  The next invariant forgets
most of the ambient space and records only which phase closures can meet.

Because there are exactly four FDE values, the relevant nerve has dimension at
most three.  This file therefore formalizes its low-dimensional skeleton
directly:

* edges are pairwise closure contacts;
* triangles are common three-phase closure contacts;
* the tetrahedron is common closure contact of all four phases.

This is deliberately lighter than introducing a generic simplicial-complex
library.  The goal of the gate is to establish the combinatorial invariant and
its epistemic meaning first.
-/

/-- Global adjacency in the phase-contact graph: two distinct phase closures meet somewhere. -/
def FDEPhaseAdjacent {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q r : FDEValue) : Prop :=
  q ≠ r ∧ ∃ w, FDEPhaseContactAt s value q r w

/-- Phase adjacency is symmetric. -/
theorem fdePhaseAdjacent_symm
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    (q r : FDEValue) :
    FDEPhaseAdjacent s value q r ↔ FDEPhaseAdjacent s value r q := by
  constructor
  · intro h
    rcases h with ⟨hqr, w, hq, hr⟩
    exact ⟨fun hrq => hqr hrq.symm, w, hr, hq⟩
  · intro h
    rcases h with ⟨hrq, w, hr, hq⟩
    exact ⟨fun hqr => hrq hqr.symm, w, hq, hr⟩

/-- The phase-contact graph has no loops. -/
theorem fdePhaseAdjacent_irrefl
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    (q : FDEValue) :
    ¬ FDEPhaseAdjacent s value q q := by
  intro h
  exact h.1 rfl

/-- Every edge of the phase-contact graph has a witness outside the local-constancy locus. -/
theorem phase_adjacency_has_unstable_witness
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {q r : FDEValue}
    (hAdj : FDEPhaseAdjacent s value q r) :
    ∃ w, ¬ TopologicallyLocallyConstantAt s value w := by
  rcases hAdj with ⟨hqr, w, hContact⟩
  exact ⟨w,
    distinct_phase_contact_implies_not_local_constancy
      s value hqr w hContact⟩

/-- Three phase closures meet at the same point. -/
def FDEPhaseTripleContactAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q r t : FDEValue) (w : W) : Prop :=
  FDEPhaseClosureAt s value q w ∧
  FDEPhaseClosureAt s value r w ∧
  FDEPhaseClosureAt s value t w

/-- A two-simplex of the phase nerve: three distinct phase closures have a common point. -/
def FDEPhaseTriangle {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (q r t : FDEValue) : Prop :=
  q ≠ r ∧ q ≠ t ∧ r ≠ t ∧
    ∃ w, FDEPhaseTripleContactAt s value q r t w

/-- Every phase-nerve triangle contains all three graph edges. -/
theorem phase_triangle_has_three_edges
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {q r t : FDEValue}
    (hTri : FDEPhaseTriangle s value q r t) :
    FDEPhaseAdjacent s value q r ∧
    FDEPhaseAdjacent s value q t ∧
    FDEPhaseAdjacent s value r t := by
  rcases hTri with ⟨hqr, hqt, hrt, w, hq, hr, ht⟩
  exact ⟨
    ⟨hqr, w, hq, hr⟩,
    ⟨hqt, w, hq, ht⟩,
    ⟨hrt, w, hr, ht⟩
  ⟩

/-- Every triangle has a common witness at which local constancy fails. -/
theorem phase_triangle_has_unstable_witness
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    {q r t : FDEValue}
    (hTri : FDEPhaseTriangle s value q r t) :
    ∃ w,
      FDEPhaseTripleContactAt s value q r t w ∧
      ¬ TopologicallyLocallyConstantAt s value w := by
  rcases hTri with ⟨hqr, _hqt, _hrt, w, hq, hr, ht⟩
  refine ⟨w, ⟨hq, hr, ht⟩, ?_⟩
  exact distinct_phase_contact_implies_not_local_constancy
    s value hqr w ⟨hq, hr⟩

/-- All four FDE phase closures meet at one point: the maximal possible nerve simplex. -/
def FDEPhaseTetrahedronAt {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue)
    (w : W) : Prop :=
  FDEPhaseClosureAt s value FDEValue.T w ∧
  FDEPhaseClosureAt s value FDEValue.F w ∧
  FDEPhaseClosureAt s value FDEValue.B w ∧
  FDEPhaseClosureAt s value FDEValue.N w

/-- Existence of the maximal three-simplex of the four-phase nerve. -/
def FDEPhaseTetrahedron {W : Type}
    (s : InteriorSemantics W) (value : W → FDEValue) : Prop :=
  ∃ w, FDEPhaseTetrahedronAt s value w

/-- A four-phase contact point is necessarily epistemically unstable. -/
theorem phase_tetrahedron_has_unstable_witness
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    (hTet : FDEPhaseTetrahedron s value) :
    ∃ w,
      FDEPhaseTetrahedronAt s value w ∧
      ¬ TopologicallyLocallyConstantAt s value w := by
  rcases hTet with ⟨w, hT, hF, hB, hN⟩
  refine ⟨w, ⟨hT, hF, hB, hN⟩, ?_⟩
  exact distinct_phase_contact_implies_not_local_constancy
    s value (by decide : FDEValue.T ≠ FDEValue.F) w ⟨hT, hF⟩

/-- The maximal simplex forces the complete six-edge contact graph on T/F/B/N. -/
theorem phase_tetrahedron_has_complete_one_skeleton
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    (hTet : FDEPhaseTetrahedron s value) :
    FDEPhaseAdjacent s value FDEValue.T FDEValue.F ∧
    FDEPhaseAdjacent s value FDEValue.T FDEValue.B ∧
    FDEPhaseAdjacent s value FDEValue.T FDEValue.N ∧
    FDEPhaseAdjacent s value FDEValue.F FDEValue.B ∧
    FDEPhaseAdjacent s value FDEValue.F FDEValue.N ∧
    FDEPhaseAdjacent s value FDEValue.B FDEValue.N := by
  rcases hTet with ⟨w, hT, hF, hB, hN⟩
  exact ⟨
    ⟨by decide, w, hT, hF⟩,
    ⟨by decide, w, hT, hB⟩,
    ⟨by decide, w, hT, hN⟩,
    ⟨by decide, w, hF, hB⟩,
    ⟨by decide, w, hF, hN⟩,
    ⟨by decide, w, hB, hN⟩
  ⟩

/-- The maximal simplex also contains each of the four triangular faces. -/
theorem phase_tetrahedron_has_four_faces
    {W : Type} (s : InteriorSemantics W) (value : W → FDEValue)
    (hTet : FDEPhaseTetrahedron s value) :
    FDEPhaseTriangle s value FDEValue.T FDEValue.F FDEValue.B ∧
    FDEPhaseTriangle s value FDEValue.T FDEValue.F FDEValue.N ∧
    FDEPhaseTriangle s value FDEValue.T FDEValue.B FDEValue.N ∧
    FDEPhaseTriangle s value FDEValue.F FDEValue.B FDEValue.N := by
  rcases hTet with ⟨w, hT, hF, hB, hN⟩
  exact ⟨
    ⟨by decide, by decide, by decide, w, hT, hF, hB⟩,
    ⟨by decide, by decide, by decide, w, hT, hF, hN⟩,
    ⟨by decide, by decide, by decide, w, hT, hB, hN⟩,
    ⟨by decide, by decide, by decide, w, hF, hB, hN⟩
  ⟩

/-!
## Sharpness: the full tetrahedron is realizable

The strongest possible closure-contact pattern is not forbidden by the abstract
topological semantics.  A four-point indiscrete space with one point carrying
each FDE value has every nonempty phase fibre dense.  Consequently all four
phase closures meet everywhere.
-/

/-- Four named points, one for each FDE phase. -/
inductive FourPhasePoint where
  | t
  | f
  | b
  | n
  deriving DecidableEq, Repr

/-- The indiscrete interior: a region has nonempty interior exactly when it is the whole space. -/
def fourPhaseIndiscreteInterior
    (A : EvidenceRegion FourPhasePoint) : EvidenceRegion FourPhasePoint :=
  fun _ => ∀ u, A u

/-- The algebraic interior semantics of the four-point indiscrete space. -/
def fourPhaseIndiscreteSemantics : InteriorSemantics FourPhasePoint where
  interior := fourPhaseIndiscreteInterior
  interior_subset := by
    intro A w h
    exact h w
  interior_monotone := by
    intro A B hAB w hA u
    exact hAB u (hA u)
  interior_idempotent := by
    intro A w
    constructor
    · intro h u
      exact h w u
    · intro h u v
      exact h v
  interior_top := by
    intro _w _u
    trivial
  interior_intersection := by
    intro A B w
    constructor
    · intro h
      constructor
      · intro u
        exact (h u).1
      · intro u
        exact (h u).2
    · intro h u
      exact ⟨h.1 u, h.2 u⟩

/-- A complete profile that realizes each of T/F/B/N at one point. -/
def fourPhaseValue : FourPhasePoint → FDEValue
  | FourPhasePoint.t => FDEValue.T
  | FourPhasePoint.f => FDEValue.F
  | FourPhasePoint.b => FDEValue.B
  | FourPhasePoint.n => FDEValue.N

/-- Every nonempty region is dense in the four-point indiscrete semantics. -/
theorem fourPhaseIndiscrete_closure_of_mem
    (A : EvidenceRegion FourPhasePoint)
    (a w : FourPhasePoint) (ha : A a) :
    fourPhaseIndiscreteSemantics.closure A w := by
  change ¬ (∀ u, ¬ A u)
  intro h
  exact h a ha

/-- The T fibre is dense. -/
theorem fourPhase_T_closure (w : FourPhasePoint) :
    FDEPhaseClosureAt fourPhaseIndiscreteSemantics
      fourPhaseValue FDEValue.T w := by
  exact fourPhaseIndiscrete_closure_of_mem
    (fdeValueRegion fourPhaseValue FDEValue.T)
    FourPhasePoint.t w (by rfl)

/-- The F fibre is dense. -/
theorem fourPhase_F_closure (w : FourPhasePoint) :
    FDEPhaseClosureAt fourPhaseIndiscreteSemantics
      fourPhaseValue FDEValue.F w := by
  exact fourPhaseIndiscrete_closure_of_mem
    (fdeValueRegion fourPhaseValue FDEValue.F)
    FourPhasePoint.f w (by rfl)

/-- The B fibre is dense. -/
theorem fourPhase_B_closure (w : FourPhasePoint) :
    FDEPhaseClosureAt fourPhaseIndiscreteSemantics
      fourPhaseValue FDEValue.B w := by
  exact fourPhaseIndiscrete_closure_of_mem
    (fdeValueRegion fourPhaseValue FDEValue.B)
    FourPhasePoint.b w (by rfl)

/-- The N fibre is dense. -/
theorem fourPhase_N_closure (w : FourPhasePoint) :
    FDEPhaseClosureAt fourPhaseIndiscreteSemantics
      fourPhaseValue FDEValue.N w := by
  exact fourPhaseIndiscrete_closure_of_mem
    (fdeValueRegion fourPhaseValue FDEValue.N)
    FourPhasePoint.n w (by rfl)

/-- Sharpness: the complete three-simplex on all four FDE phases is realizable. -/
theorem full_FDE_phase_tetrahedron_realizable :
    FDEPhaseTetrahedron fourPhaseIndiscreteSemantics fourPhaseValue := by
  refine ⟨FourPhasePoint.t, ?_⟩
  exact ⟨
    fourPhase_T_closure FourPhasePoint.t,
    fourPhase_F_closure FourPhasePoint.t,
    fourPhase_B_closure FourPhasePoint.t,
    fourPhase_N_closure FourPhasePoint.t
  ⟩

/-- In the sharpness model every point is non-locally-constant. -/
theorem fourPhase_indiscrete_nowhere_locally_constant
    (w : FourPhasePoint) :
    ¬ TopologicallyLocallyConstantAt
      fourPhaseIndiscreteSemantics fourPhaseValue w := by
  have hTF : FDEPhaseContactAt fourPhaseIndiscreteSemantics
      fourPhaseValue FDEValue.T FDEValue.F w :=
    ⟨fourPhase_T_closure w, fourPhase_F_closure w⟩
  exact distinct_phase_contact_implies_not_local_constancy
    fourPhaseIndiscreteSemantics fourPhaseValue
    (by decide) w hTF

/-!
## Interpretation

Gate 10 compresses an arbitrarily complicated state space to a combinatorial
contact invariant on the four complete FDE phases.

An edge records that two phase closures meet.  A triangle records genuine
three-way contact at one state; pairwise adjacency alone is not used as a
substitute for this stronger condition.  The tetrahedron records simultaneous
adherence of all four phases.

Every positive-dimensional simplex has an epistemically unstable witness.  The
full tetrahedron is realizable on an indiscrete four-point space, so the abstract
semantics places no dimension-lowering restriction on the phase nerve by
itself.  Any prohibition of higher-order contacts must therefore come from
additional structure, such as separation assumptions, Alexandrov-frame
constraints, probability dynamics, or formula-specific geometry.

This also clarifies the paper-visualization strategy.  The phase nerve is a
finite combinatorial object that can be drawn as a graph, filled triangle, or
tetrahedron without pretending that Euclidean drawing coordinates constitute
the underlying topology.
-/

end PEL4
