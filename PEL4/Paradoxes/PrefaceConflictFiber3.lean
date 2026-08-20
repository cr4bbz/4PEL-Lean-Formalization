import Lean.Elab.Tactic.Omega
import PEL4.Paradoxes.PrefaceConflictIncidence3

namespace PEL4.Paradoxes
namespace ConflictIncidence3

/-!
# A tetrahedral fixed-marginal fiber

Fix the symmetric three-claim coarse data

  b1 = b2 = b3 = m
  d = 2m.

This corresponds to

  S = 3m,
  p = m,
  kappa = 1/2,
  rho = 3/2,
  q = r = 1/4.

Inside that single coarse point, the full incidence profile still has three
degrees of freedom.  The overlap coordinates satisfy

  x12 + x13 + x23 + 2*x123 = m,

and the singleton coordinates are forced by

  x1 = x23 + x123,
  x2 = x13 + x123,
  x3 = x12 + x123.

After using `2*x123` as the fourth weighted coordinate and normalizing by `m`,
the continuous fiber is a standard `Delta^3`.
-/

/-- Necessary equations for every incidence profile in the symmetric mid-fiber. -/
theorem symmetric_mid_fiber_equations
    (s : ConflictIncidence3)
    (m : Nat)
    (h1 : s.b1 = m)
    (h2 : s.b2 = m)
    (h3 : s.b3 = m)
    (hd : s.d = 2 * m) :
    s.x12 + s.x13 + s.x23 + 2 * s.x123 = m ∧
      s.x1 = s.x23 + s.x123 ∧
      s.x2 = s.x13 + s.x123 ∧
      s.x3 = s.x12 + s.x123 := by
  have hdec := redundancy_incidence_decomposition s
  have hb1 := h1
  have hb2 := h2
  have hb3 := h3
  simp [totalLocal, h1, h2, h3, hd] at hdec
  simp [b1] at hb1
  simp [b2] at hb2
  simp [b3] at hb3
  omega

/-- Construct an incidence profile from any nonnegative weighted-overlap point
on the tetrahedral equation

  x12 + x13 + x23 + 2*x123 = m.

The singleton coordinates are the opposite pair mass plus the triple mass. -/
def symmetricMidFiberFromOverlap
    (m x12 x13 x23 x123 : Nat)
    (h : x12 + x13 + x23 + 2 * x123 = m) : ConflictIncidence3 :=
  { x1 := x23 + x123
  , x2 := x13 + x123
  , x3 := x12 + x123
  , x12 := x12
  , x13 := x13
  , x23 := x23
  , x123 := x123
  , d := 2 * m
  , total := by omega }

/-- The construction always lands at the same carrier and the same three local
marginals. -/
theorem symmetricMidFiberFromOverlap_projection
    (m x12 x13 x23 x123 : Nat)
    (h : x12 + x13 + x23 + 2 * x123 = m) :
    let s := symmetricMidFiberFromOverlap m x12 x13 x23 x123 h
    s.d = 2 * m ∧ s.b1 = m ∧ s.b2 = m ∧ s.b3 = m := by
  dsimp [symmetricMidFiberFromOverlap]
  simp [b1, b2, b3]
  omega

/-- Hence every weighted-overlap lattice point has the same raw triangle
projection: carrier `2m`, total local mass `3m`, and peak `m`. -/
theorem symmetricMidFiberFromOverlap_coarse
    (m x12 x13 x23 x123 : Nat)
    (h : x12 + x13 + x23 + 2 * x123 = m) :
    let s := symmetricMidFiberFromOverlap m x12 x13 x23 x123 h
    s.d = 2 * m ∧ s.totalLocal = 3 * m ∧ s.peak = m := by
  have hp := symmetricMidFiberFromOverlap_projection m x12 x13 x23 x123 h
  dsimp at hp ⊢
  rcases hp with ⟨hd, h1, h2, h3⟩
  simp [totalLocal, peak, h1, h2, h3, hd]

/-- Existing Fiber A is the pair vertex of this tetrahedral family. -/
example :
    let s := symmetricMidFiberFromOverlap 3 3 0 0 0 (by omega)
    s.b1 = 3 ∧ s.b2 = 3 ∧ s.b3 = 3 ∧
      s.x12 = 3 ∧ s.x123 = 0 := by
  decide

/-- Existing Fiber B lies on the edge joining the `{1,2}` pair direction to
triple conflict. -/
example :
    let s := symmetricMidFiberFromOverlap 3 1 0 0 1 (by omega)
    s.b1 = 3 ∧ s.b2 = 3 ∧ s.b3 = 3 ∧
      s.x12 = 1 ∧ s.x123 = 1 := by
  decide

end ConflictIncidence3
end PEL4.Paradoxes
