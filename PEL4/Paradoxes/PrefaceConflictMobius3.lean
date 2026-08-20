import Std.Tactic.Omega
import PEL4.Paradoxes.PrefaceConflictIncidence3

namespace PEL4.Paradoxes
namespace ConflictIncidence3

/-!
# Three-claim co-conflict / Möbius coordinates

The exact incidence coordinates `x_A` describe which local-glut pattern occurs.
An equivalent cumulative view records joint co-conflict masses:

  j12  = mass where propositions 1 and 2 are both B,
  j13  = mass where propositions 1 and 3 are both B,
  j23  = mass where propositions 2 and 3 are both B,
  j123 = mass where all three are B.

These are Boolean-lattice upper-set sums of the exact incidence coordinates.
The inverse relations are inclusion-exclusion / Möbius identities.
-/

/-- Pairwise co-conflict masses. -/
def j12 (s : ConflictIncidence3) : Nat := s.x12 + s.x123
def j13 (s : ConflictIncidence3) : Nat := s.x13 + s.x123
def j23 (s : ConflictIncidence3) : Nat := s.x23 + s.x123

/-- Triple co-conflict mass. -/
def j123 (s : ConflictIncidence3) : Nat := s.x123

/-- Raw inclusion-exclusion identity for the carrier union:

  d + j12 + j13 + j23 = b1 + b2 + b3 + j123.

Normalized by `d`, this is

  1 = M1 + M2 + M3 - M12 - M13 - M23 + M123.
-/
theorem conflict_inclusion_exclusion (s : ConflictIncidence3) :
    s.d + s.j12 + s.j13 + s.j23 =
      s.b1 + s.b2 + s.b3 + s.j123 := by
  have htotal := s.total
  simp [j12, j13, j23, j123, b1, b2, b3]
  omega

/-- Pair exact-pattern masses are recovered from cumulative co-conflict masses
by subtracting the triple interaction.  Written additively to avoid truncated
natural-number subtraction. -/
theorem pair_mobius_relations (s : ConflictIncidence3) :
    s.x12 + s.j123 = s.j12 ∧
      s.x13 + s.j123 = s.j13 ∧
      s.x23 + s.j123 = s.j23 := by
  simp [j12, j13, j23, j123]

/-- Singleton exact-pattern masses are the first-order marginals corrected by
pair and triple co-conflict terms.  These are the additive Nat forms of

  x1 = b1 - j12 - j13 + j123,
  x2 = b2 - j12 - j23 + j123,
  x3 = b3 - j13 - j23 + j123.
-/
theorem singleton_mobius_relations (s : ConflictIncidence3) :
    s.x1 + s.j12 + s.j13 = s.b1 + s.j123 ∧
      s.x2 + s.j12 + s.j23 = s.b2 + s.j123 ∧
      s.x3 + s.j13 + s.j23 = s.b3 + s.j123 := by
  simp [j12, j13, j23, j123, b1, b2, b3]
  omega

/-- Redundancy can be read directly from cumulative co-conflict moments:

  S + j123 = d + j12 + j13 + j23.

Equivalently,

  S - d = j12 + j13 + j23 - j123.
-/
theorem redundancy_from_coconflict (s : ConflictIncidence3) :
    s.totalLocal + s.j123 =
      s.d + s.j12 + s.j13 + s.j23 := by
  have hie := conflict_inclusion_exclusion s
  simp [totalLocal] at hie ⊢
  omega

/-!
## The earlier fixed-marginal fiber in co-conflict coordinates

`fiberA` and `fiberB` have the same first-order marginals but distinct higher
moments.  Thus the hidden fiber dimensions are concretely higher-order
co-conflict degrees of freedom.
-/

/-- Fiber A: all higher-order mass is pairwise `{1,2}` conflict. -/
example :
    fiberA.j12 = 3 ∧ fiberA.j13 = 0 ∧ fiberA.j23 = 0 ∧ fiberA.j123 = 0 := by
  decide

/-- Fiber B: pairwise cumulative moments coexist with genuine triple conflict. -/
example :
    fiberB.j12 = 2 ∧ fiberB.j13 = 1 ∧ fiberB.j23 = 1 ∧ fiberB.j123 = 1 := by
  decide

/-- Same first-order marginals do not determine second- and third-order
co-conflict moments. -/
theorem same_marginals_different_coconflict :
    fiberA.b1 = fiberB.b1 ∧
    fiberA.b2 = fiberB.b2 ∧
    fiberA.b3 = fiberB.b3 ∧
    (fiberA.j12 ≠ fiberB.j12 ∨
      fiberA.j13 ≠ fiberB.j13 ∨
      fiberA.j23 ≠ fiberB.j23 ∨
      fiberA.j123 ≠ fiberB.j123) := by
  decide

end ConflictIncidence3
end PEL4.Paradoxes
