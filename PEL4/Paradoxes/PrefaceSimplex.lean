import Lean.Elab.Tactic.Omega

namespace PEL4.Paradoxes

/--
A finite-count representation of an arbitrary three-claim one-error Preface model.

`a` counts the all-correct worlds. `e1`, `e2`, and `e3` count the worlds in which
exactly the corresponding claim is false. `m` is the total mass, and `k / m`
is the Lockean threshold.
-/
structure PrefaceSimplex3 where
  a : Nat
  e1 : Nat
  e2 : Nat
  e3 : Nat
  m : Nat
  k : Nat
  total : a + e1 + e2 + e3 = m

/--
The characteristic Preface constraints in the one-error simplex.

For each claim `pi`, local acceptance means its error mass `ei` is at most
`m-k`. Acceptance of global fallibility means the all-correct mass `a` is at
most `m-k`. Thus every simplex coordinate is bounded by the same cap.
-/
def PrefaceSimplex3.InRegion (s : PrefaceSimplex3) : Prop :=
  s.a ≤ s.m - s.k ∧
  s.e1 ≤ s.m - s.k ∧
  s.e2 ≤ s.m - s.k ∧
  s.e3 ≤ s.m - s.k

/--
Any three-claim one-error Preface state must satisfy the same `3/4` upper
threshold boundary as the symmetric model.

Geometrically, the Preface region is the intersection of the probability
simplex with the four coordinate half-spaces `x_i ≤ 1-c`. If that intersection
is non-empty, the four capped coordinates must still sum to the full mass.
-/
theorem preface_simplex3_threshold_necessary
    (s : PrefaceSimplex3)
    (hk : s.k ≤ s.m)
    (h : s.InRegion) :
    4 * s.k ≤ 3 * s.m := by
  rcases h with ⟨ha, he1, he2, he3⟩
  have htotal := s.total
  have hsub : s.m - s.k + s.k = s.m := Nat.sub_add_cancel hk
  omega

/--
Equivalently, a threshold strictly above `3/4` makes the three-claim one-error
Preface region empty, regardless of how asymmetrically the error mass is
allocated.
-/
theorem preface_simplex3_above_three_quarters_empty
    (s : PrefaceSimplex3)
    (hk : s.k ≤ s.m)
    (hhigh : 3 * s.m < 4 * s.k) :
    ¬ s.InRegion := by
  intro h
  have hbound := preface_simplex3_threshold_necessary s hk h
  omega

/-- The symmetric control point `(1,1,1,1)` at threshold `3/4` lies on the boundary. -/
def symmetricSimplex3 : PrefaceSimplex3 :=
  { a := 1, e1 := 1, e2 := 1, e3 := 1, m := 4, k := 3, total := by decide }

example : symmetricSimplex3.InRegion := by
  decide

end PEL4.Paradoxes
