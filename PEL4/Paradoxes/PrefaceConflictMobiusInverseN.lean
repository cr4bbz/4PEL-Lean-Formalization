import PEL4.Paradoxes.PrefaceConflictMobiusN

namespace PEL4.Paradoxes

/-!
# Arbitrary-arity Möbius reconstruction

`PrefaceConflictMobiusN.lean` defined the cumulative co-conflict hierarchy

  J_Q = sum_{A superset Q} x_A.

This module develops the inverse direction.  Instead of starting with the
closed alternating-sum formula, we use the equivalent finite-difference form
of Möbius inversion on the Boolean cube.

For a target incidence pattern, a `true` coordinate is retained as a required
coordinate.  A `false` coordinate applies the finite difference

  F(..., false, ...) - F(..., true, ...).

Iterating this through all coordinates cancels every strict superset of the
target and leaves exactly the target-pattern mass.
-/

/-- Integer-valued zeta contribution of one exact incidence pattern. -/
def zetaCell (query pattern : List Bool) (mass : Nat) : Int :=
  if patternContains query pattern then Int.ofNat mass else 0

/-- Möbius inversion as iterated coordinate-wise finite differences.

Applied to a function `F` on Boolean query patterns, this follows the target
pattern from left to right.  Required (`true`) coordinates are fixed; absent
(`false`) coordinates subtract the branch in which that coordinate is forced
present. -/
def mobiusRecover : List Bool → (List Bool → Int) → Int
| [], F => F []
| true :: rest, F =>
    mobiusRecover rest (fun q => F (true :: q))
| false :: rest, F =>
    mobiusRecover rest (fun q => F (false :: q)) -
      mobiusRecover rest (fun q => F (true :: q))

/-- The Möbius operator annihilates the zero function. -/
theorem mobiusRecover_zero :
    ∀ target : List Bool,
      mobiusRecover target (fun _ => 0) = 0
| [] => rfl
| true :: rest => by
    exact mobiusRecover_zero rest
| false :: rest => by
    simp [mobiusRecover, mobiusRecover_zero rest]

/-- Möbius recovery is additive over integer-valued query functions. -/
theorem mobiusRecover_add :
    ∀ (target : List Bool) (F G : List Bool → Int),
      mobiusRecover target (fun q => F q + G q) =
        mobiusRecover target F + mobiusRecover target G
| [], F, G => rfl
| true :: rest, F, G => by
    simpa [mobiusRecover] using
      mobiusRecover_add rest
        (fun q => F (true :: q))
        (fun q => G (true :: q))
| false :: rest, F, G => by
    have hfalse := mobiusRecover_add rest
      (fun q => F (false :: q))
      (fun q => G (false :: q))
    have htrue := mobiusRecover_add rest
      (fun q => F (true :: q))
      (fun q => G (true :: q))
    change
      (mobiusRecover rest (fun q => F (false :: q) + G (false :: q)) -
        mobiusRecover rest (fun q => F (true :: q) + G (true :: q))) =
      (mobiusRecover rest (fun q => F (false :: q)) -
        mobiusRecover rest (fun q => F (true :: q))) +
      (mobiusRecover rest (fun q => G (false :: q)) -
        mobiusRecover rest (fun q => G (true :: q)))
    rw [hfalse, htrue]
    omega

/-- On one zeta basis vector, Möbius inversion is a Kronecker delta: all
strict supersets cancel and exactly the target pattern survives. -/
theorem mobiusRecover_zetaCell :
    ∀ (target pattern : List Bool) (mass : Nat),
      target.length = pattern.length →
      mobiusRecover target (fun q => zetaCell q pattern mass) =
        if target = pattern then Int.ofNat mass else 0
| [], [], mass, _ => by
    simp [mobiusRecover, zetaCell, patternContains]
| [], _ :: _, _, hlen => by
    simp at hlen
| _ :: _, [], _, hlen => by
    simp at hlen
| false :: ts, false :: ps, mass, hlen => by
    simp at hlen
    have ih := mobiusRecover_zetaCell ts ps mass hlen
    simpa [mobiusRecover, zetaCell, patternContains, mobiusRecover_zero] using ih
| false :: ts, true :: ps, mass, hlen => by
    simp [mobiusRecover, zetaCell, patternContains]
| true :: ts, false :: ps, mass, hlen => by
    simp [mobiusRecover, zetaCell, patternContains, mobiusRecover_zero]
| true :: ts, true :: ps, mass, hlen => by
    simp at hlen
    have ih := mobiusRecover_zetaCell ts ps mass hlen
    simpa [mobiusRecover, zetaCell, patternContains] using ih

/-- Exact mass of one incidence pattern.  Repeated cells with the same pattern
are intentionally summed. -/
def exactPatternMass {n : Nat}
    (target : List Bool) : List (ConflictPatternCell n) → Nat
| [] => 0
| c :: cs =>
    (if c.pattern = target then c.mass else 0) + exactPatternMass target cs

/-- Integer mirror of the cumulative co-conflict mass. -/
def coConflictMassInt {n : Nat}
    (query : List Bool) : List (ConflictPatternCell n) → Int
| [] => 0
| c :: cs => zetaCell query c.pattern c.mass + coConflictMassInt query cs

/-- The integer mirror agrees exactly with the already-defined natural-valued
co-conflict coordinate. -/
theorem coConflictMassInt_eq_ofNat {n : Nat}
    (query : List Bool) :
    ∀ cells : List (ConflictPatternCell n),
      coConflictMassInt query cells = Int.ofNat (coConflictMass query cells)
| [] => by simp [coConflictMassInt, coConflictMass]
| c :: cs => by
    have ih := coConflictMassInt_eq_ofNat query cs
    by_cases h : patternContains query c.pattern = true
    · simp [coConflictMassInt, coConflictMass, zetaCell, h, ih]
    · have hf : patternContains query c.pattern = false := by
        cases hx : patternContains query c.pattern <;> simp_all
      simp [coConflictMassInt, coConflictMass, zetaCell, hf, ih]

/-- Generic reconstruction theorem.

For every target pattern of the correct arity, iterated Möbius differences of
the complete co-conflict hierarchy recover exactly the mass assigned to that
incidence pattern.
-/
theorem mobius_reconstructs_exact_pattern {n : Nat}
    (target : List Bool)
    (hlen : target.length = n) :
    ∀ cells : List (ConflictPatternCell n),
      mobiusRecover target (fun q => coConflictMassInt q cells) =
        Int.ofNat (exactPatternMass target cells)
| [] => by
    change mobiusRecover target (fun _ => 0) = 0
    exact mobiusRecover_zero target
| c :: cs => by
    have hcellLen : target.length = c.pattern.length :=
      hlen.trans c.arity.symm
    have hcell := mobiusRecover_zetaCell target c.pattern c.mass hcellLen
    have ih := mobius_reconstructs_exact_pattern target hlen cs
    change mobiusRecover target
        (fun q => zetaCell q c.pattern c.mass + coConflictMassInt q cs) =
      Int.ofNat ((if c.pattern = target then c.mass else 0) +
        exactPatternMass target cs)
    rw [mobiusRecover_add]
    rw [hcell, ih]
    by_cases heq : c.pattern = target
    · have heq' : target = c.pattern := heq.symm
      simp [heq, heq']
    · have hne : target ≠ c.pattern := by
        intro h
        exact heq h.symm
      simp [heq, hne]

namespace ConflictIncidenceN

/-- Exact incidence coordinate exposed at profile level. -/
def exactMass {n : Nat} (s : ConflictIncidenceN n) (target : List Bool) : Nat :=
  exactPatternMass target s.cells

/-- Information-completeness of the full co-conflict hierarchy.

If all cumulative co-conflict coordinates are available, the exact mass of any
incidence pattern can be reconstructed by Boolean Möbius inversion. -/
theorem full_coconflict_hierarchy_reconstructs_exact_mass {n : Nat}
    (s : ConflictIncidenceN n)
    (target : List Bool)
    (hlen : target.length = n) :
    mobiusRecover target (fun q => Int.ofNat (s.coConflict q)) =
      Int.ofNat (s.exactMass target) := by
  have hfun :
      (fun q => Int.ofNat (s.coConflict q)) =
        (fun q => coConflictMassInt q s.cells) := by
    funext q
    symm
    exact coConflictMassInt_eq_ofNat q s.cells
  rw [hfun]
  exact mobius_reconstructs_exact_pattern target hlen s.cells

end ConflictIncidenceN

/-!
## Philosophical consequence

The earlier projection results established underdetermination: local threshold
beliefs, global FDE state, carrier mass, `(q,r)`, and even all first-order local
glut marginals can agree while higher-order incidence differs.

The theorem above identifies a natural information-complete endpoint.  The
*entire* hierarchy of simultaneous co-conflict masses is sufficient to recover
every exact incidence coordinate.  Thus information is not destroyed by the
zeta representation itself; it is lost only when the hierarchy is truncated.
-/

end PEL4.Paradoxes
