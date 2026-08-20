import Lean.Elab.Tactic.Omega
import PEL4.Paradoxes.PrefaceConflictFiber3
import PEL4.Paradoxes.PrefaceConflictMobius3

namespace PEL4.Paradoxes
namespace ConflictIncidence3

/-!
# Three-claim support conflict nerves

The fixed-marginal tetrahedral fiber already contains qualitatively different
support nerves.  All examples below have

  d = 6,
  b1 = b2 = b3 = 3,
  S = 9,
  p = 3,

and therefore project to the same coarse conflict-triangle point.  Yet the
positive co-conflict pattern can be disconnected, cyclic, or fully filled.

This file formalizes the finite combinatorial signatures and their Euler
counts.  It does not claim a formal homology computation; that would require a
separate simplicial-homology layer.
-/

/-- The symmetric pair-balanced point of the tetrahedral fiber:

  x12 = x13 = x23 = 1, x123 = 0.

Its singleton masses are also all one, so the carrier is six and every local
marginal is three. -/
def fiberCycle : ConflictIncidence3 :=
  symmetricMidFiberFromOverlap 3 1 1 1 0 (by omega)

/-- Coarse data retained by the triangle projection. -/
def sameCoarse3 (s t : ConflictIncidence3) : Prop :=
  s.d = t.d ∧
  s.b1 = t.b1 ∧ s.b2 = t.b2 ∧ s.b3 = t.b3 ∧
  s.totalLocal = t.totalLocal ∧ s.peak = t.peak

/-- The pair-balanced cycle profile occupies the same coarse fiber as `fiberA`. -/
theorem fiberA_cycle_same_coarse : sameCoarse3 fiberA fiberCycle := by
  decide

/-- It also occupies the same coarse fiber as `fiberB`. -/
theorem fiberCycle_B_same_coarse : sameCoarse3 fiberCycle fiberB := by
  decide

/-- `fiberA` has three vertices but only the `{1,2}` support edge. -/
theorem fiberA_support_nerve_signature :
    0 < fiberA.b1 ∧ 0 < fiberA.b2 ∧ 0 < fiberA.b3 ∧
    0 < fiberA.j12 ∧ fiberA.j13 = 0 ∧ fiberA.j23 = 0 ∧
    fiberA.j123 = 0 := by
  decide

/-- `fiberCycle` has all three pair edges but no filled triple simplex. -/
theorem fiberCycle_support_nerve_signature :
    0 < fiberCycle.b1 ∧ 0 < fiberCycle.b2 ∧ 0 < fiberCycle.b3 ∧
    0 < fiberCycle.j12 ∧ 0 < fiberCycle.j13 ∧ 0 < fiberCycle.j23 ∧
    fiberCycle.j123 = 0 := by
  decide

/-- `fiberB` has positive support on every vertex, every pair edge, and the
triple simplex. -/
theorem fiberB_support_nerve_signature :
    0 < fiberB.b1 ∧ 0 < fiberB.b2 ∧ 0 < fiberB.b3 ∧
    0 < fiberB.j12 ∧ 0 < fiberB.j13 ∧ 0 < fiberB.j23 ∧
    0 < fiberB.j123 := by
  decide

/-- Indicator used in the finite Euler count of the support nerve. -/
def supportIndicator (x : Nat) : Int := if 0 < x then 1 else 0

/-- Three-vertex support-nerve Euler count

  chi = V - E + F,

where vertices are positive first-order conflict marginals, edges are positive
pair co-conflicts, and the face is positive triple co-conflict. -/
def supportNerveEuler3 (s : ConflictIncidence3) : Int :=
  supportIndicator s.b1 + supportIndicator s.b2 + supportIndicator s.b3 -
    (supportIndicator s.j12 + supportIndicator s.j13 + supportIndicator s.j23) +
    supportIndicator s.j123

/-- The three support nerves have distinct Euler counts despite identical
coarse projections. -/
theorem same_coarse_distinct_support_nerve_euler :
    sameCoarse3 fiberA fiberCycle ∧
    sameCoarse3 fiberCycle fiberB ∧
    supportNerveEuler3 fiberA = 2 ∧
    supportNerveEuler3 fiberCycle = 0 ∧
    supportNerveEuler3 fiberB = 1 := by
  decide

/-!
## Topological reading

At support threshold one, the explicit signatures are respectively:

* `fiberA`: one edge plus one isolated vertex,
* `fiberCycle`: the boundary of a triangle with no 2-simplex,
* `fiberB`: the filled 2-simplex.

Thus the same local marginals and the same `(q,r)` projection can hide support
nerves with different combinatorial topology.  The theorem above certifies this
already at the Euler-count level, while the signatures retain the full
three-vertex support pattern.
-/

end ConflictIncidence3
end PEL4.Paradoxes
