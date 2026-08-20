import Std.Tactic.Omega
import PEL4.Paradoxes.PrefaceConflictTopologyN

namespace PEL4.Paradoxes

/-!
# Three-claim conflict incidence simplex

For three conjuncts, every world in the latent conflict carrier has one of the
seven nonempty local-glut incidence patterns

  {1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}.

Their finite masses are the coordinates of a denominator-free `Delta^6`.
This module makes the projection from that full incidence geometry to the
coarser local marginals and Latent-Conflict Triangle explicit.
-/

structure ConflictIncidence3 where
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x12 : Nat
  x13 : Nat
  x23 : Nat
  x123 : Nat
  d : Nat
  total : x1 + x2 + x3 + x12 + x13 + x23 + x123 = d

namespace ConflictIncidence3

/-- Marginal local-glut mass of proposition 1. -/
def b1 (s : ConflictIncidence3) : Nat :=
  s.x1 + s.x12 + s.x13 + s.x123

/-- Marginal local-glut mass of proposition 2. -/
def b2 (s : ConflictIncidence3) : Nat :=
  s.x2 + s.x12 + s.x23 + s.x123

/-- Marginal local-glut mass of proposition 3. -/
def b3 (s : ConflictIncidence3) : Nat :=
  s.x3 + s.x13 + s.x23 + s.x123

/-- Sum of all three local glut marginals. -/
def totalLocal (s : ConflictIncidence3) : Nat := s.b1 + s.b2 + s.b3

/-- Largest local glut marginal. -/
def peak (s : ConflictIncidence3) : Nat := max s.b1 (max s.b2 s.b3)

/-- The total local multiplicity is the incidence-size expectation in raw
finite counts: singleton cells count once, pair cells twice, and the triple cell
three times. -/
theorem totalLocal_incidence_identity (s : ConflictIncidence3) :
    s.totalLocal =
      s.x1 + s.x2 + s.x3 +
      2 * (s.x12 + s.x13 + s.x23) +
      3 * s.x123 := by
  simp [totalLocal, b1, b2, b3]
  omega

/-- Exact redundancy decomposition for three claims.

The excess multiplicity above the carrier mass is one copy of every pair-only
cell plus two extra copies of the triple cell:

  S = d + x12 + x13 + x23 + 2*x123.
-/
theorem redundancy_incidence_decomposition (s : ConflictIncidence3) :
    s.totalLocal =
      s.d + s.x12 + s.x13 + s.x23 + 2 * s.x123 := by
  have hmult := totalLocal_incidence_identity s
  have htotal := s.total
  omega

/-- Because every carrier pattern is nonempty, carrier mass is bounded by total
local multiplicity. -/
theorem carrier_le_totalLocal (s : ConflictIncidence3) :
    s.d ≤ s.totalLocal := by
  have h := redundancy_incidence_decomposition s
  omega

/-- Each local marginal is contained in the carrier. -/
theorem b1_le_carrier (s : ConflictIncidence3) : s.b1 ≤ s.d := by
  have htotal := s.total
  simp [b1]
  omega

theorem b2_le_carrier (s : ConflictIncidence3) : s.b2 ≤ s.d := by
  have htotal := s.total
  simp [b2]
  omega

theorem b3_le_carrier (s : ConflictIncidence3) : s.b3 ≤ s.d := by
  have htotal := s.total
  simp [b3]
  omega

/-- Forget higher-order incidence information and retain only the three local
marginals.  This is the raw projection from `Delta^6` toward the conflict
triangle. -/
def toTopologyN (s : ConflictIncidence3) : ConflictTopologyN :=
  { d := s.d
  , local := [s.b1, s.b2, s.b3]
  , union_le_sum := by
      have htotal := s.total
      simp [b1, b2, b3]
      omega
  , local_le_carrier := by
      simp [AllLE, b1_le_carrier s, b2_le_carrier s, b3_le_carrier s] }

/-- The full incidence simplex projects into the same raw triangle chain
`d <= S <= 3p <= 3d`. -/
theorem projection_triangle_chain (s : ConflictIncidence3) :
    s.d ≤ s.totalLocal ∧
      s.totalLocal ≤ 3 * s.peak ∧
      3 * s.peak ≤ 3 * s.d := by
  have h := ConflictTopologyN.raw_triangle_chain (s.toTopologyN)
  simpa [toTopologyN, ConflictTopologyN.totalLocal, ConflictTopologyN.arity,
    ConflictTopologyN.peak, totalLocal, peak, maxNatList] using h

/-- Pairwise-or-higher incidence mass.  This is information discarded by the
marginal projection. -/
def overlapMass (s : ConflictIncidence3) : Nat :=
  s.x12 + s.x13 + s.x23 + s.x123

/-- Triple-incidence mass, another higher-order coordinate invisible to `(q,r)`
once carrier, total local mass, and peak are fixed. -/
def tripleMass (s : ConflictIncidence3) : Nat := s.x123

/-!
## Triangle boundaries as faces of the incidence simplex
-/

/-- Bottom edge `r = 0`: exact absence of redundancy is equivalent to all
pairwise and triple incidence coordinates vanishing.  The incidence profile is
therefore confined to the singleton face spanned by `{1}`, `{2}`, `{3}`. -/
theorem no_redundancy_iff_singleton_face (s : ConflictIncidence3) :
    s.totalLocal = s.d ↔
      s.x12 = 0 ∧ s.x13 = 0 ∧ s.x23 = 0 ∧ s.x123 = 0 := by
  constructor
  · intro h
    have hdec := redundancy_incidence_decomposition s
    omega
  · rintro ⟨h12, h13, h23, h123⟩
    have hdec := redundancy_incidence_decomposition s
    omega

/-- Right edge for proposition 1: if its local glut marginal fills the whole
carrier, then no positive-mass incidence pattern can omit proposition 1. -/
theorem b1_full_carrier_iff_no_pattern_without_1 (s : ConflictIncidence3) :
    s.b1 = s.d ↔ s.x2 = 0 ∧ s.x3 = 0 ∧ s.x23 = 0 := by
  have htotal := s.total
  constructor
  · intro h
    simp [b1] at h
    omega
  · rintro ⟨h2, h3, h23⟩
    simp [b1]
    omega

/-- Maximum redundancy `S = 3d` collapses the whole incidence simplex to the
triple-conflict vertex: every carrier world is glutty in all three conjuncts. -/
theorem maximal_redundancy_forces_triple_vertex
    (s : ConflictIncidence3)
    (hmax : s.totalLocal = 3 * s.d) :
    s.x123 = s.d ∧
      s.x1 = 0 ∧ s.x2 = 0 ∧ s.x3 = 0 ∧
      s.x12 = 0 ∧ s.x13 = 0 ∧ s.x23 = 0 := by
  have hdec := redundancy_incidence_decomposition s
  have htotal := s.total
  omega

/-!
## A nontrivial fiber over one triangle point

Both profiles below have carrier `d = 6` and identical local marginals
`(3,3,3)`.  Hence they have the same total local mass `S = 9`, the same peak
`p = 3`, and therefore the same normalized triangle coordinates

  q = r = 1/4.

But their higher-order incidence structures differ substantially.
-/

/-- Three units of `{1,2}` conflict plus three units of singleton `{3}`. -/
def fiberA : ConflictIncidence3 :=
  { x1 := 0, x2 := 0, x3 := 3
  , x12 := 3, x13 := 0, x23 := 0, x123 := 0
  , d := 6
  , total := by omega }

/-- A mixture containing singleton, pair, and genuine triple conflict. -/
def fiberB : ConflictIncidence3 :=
  { x1 := 1, x2 := 1, x3 := 2
  , x12 := 1, x13 := 0, x23 := 0, x123 := 1
  , d := 6
  , total := by omega }

example : fiberA.b1 = 3 ∧ fiberA.b2 = 3 ∧ fiberA.b3 = 3 := by decide
example : fiberB.b1 = 3 ∧ fiberB.b2 = 3 ∧ fiberB.b3 = 3 := by decide

/-- The two microstructures are indistinguishable by carrier, local marginals,
total multiplicity, and peak. -/
theorem fiber_same_coarse_projection :
    fiberA.d = fiberB.d ∧
    fiberA.b1 = fiberB.b1 ∧
    fiberA.b2 = fiberB.b2 ∧
    fiberA.b3 = fiberB.b3 ∧
    fiberA.totalLocal = fiberB.totalLocal ∧
    fiberA.peak = fiberB.peak := by
  decide

/-- Yet their higher-order conflict geometry is genuinely different. -/
theorem fiber_hidden_structure_differs :
    fiberA.overlapMass ≠ fiberB.overlapMass ∧
    fiberA.tripleMass ≠ fiberB.tripleMass := by
  decide

end ConflictIncidence3

end PEL4.Paradoxes
