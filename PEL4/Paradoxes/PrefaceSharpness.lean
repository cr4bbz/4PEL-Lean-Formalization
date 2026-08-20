import Std.Tactic.Omega

namespace PEL4.Paradoxes

/-!
# Sharp latent-conflict geometry

This module characterizes equality in the latent-conflict carrier bound.
All quantities are finite counts, so the results are denominator-free.

For a joint conjunction, let

* `t,b,n,f` be its FDE cell counts,
* `k` be the positive/negative belief threshold,
* `carrier` count worlds in which at least one conjunct is locally B.

Write the positive and negative support counts as threshold plus slack:

  positive = k + deltaPos
  negative = k + deltaNeg

and write local carrier mass as joint-B mass plus waste:

  carrier = b + waste.

Then the exact accounting identity is

  m + carrier = 2*k + deltaPos + deltaNeg + n + waste.

Hence the lower bound `2*k <= m + carrier` is sharp exactly when all four
non-negative inefficiency terms vanish.
-/

structure SharpConflictProfile where
  t : Nat
  b : Nat
  n : Nat
  f : Nat
  carrier : Nat
  m : Nat
  k : Nat
  total : t + b + n + f = m

namespace SharpConflictProfile

def positive (s : SharpConflictProfile) : Nat := s.t + s.b
def negative (s : SharpConflictProfile) : Nat := s.f + s.b

/-- Exact decomposition of excess local conflict above the `2k-m` minimum. -/
theorem sharpness_decomposition
    (s : SharpConflictProfile)
    (deltaPos deltaNeg waste : Nat)
    (hpos : s.positive = s.k + deltaPos)
    (hneg : s.negative = s.k + deltaNeg)
    (hcarrier : s.carrier = s.b + waste) :
    s.m + s.carrier =
      2 * s.k + deltaPos + deltaNeg + s.n + waste := by
  simp [positive, negative] at hpos hneg
  omega

/-- Equality in the latent-conflict carrier bound leaves no room for positive
slack, negative slack, joint gap mass, or unused local conflict. -/
theorem sharpness_forces_zero_inefficiency
    (s : SharpConflictProfile)
    (deltaPos deltaNeg waste : Nat)
    (hpos : s.positive = s.k + deltaPos)
    (hneg : s.negative = s.k + deltaNeg)
    (hcarrier : s.carrier = s.b + waste)
    (hsharp : s.m + s.carrier = 2 * s.k) :
    deltaPos = 0 ∧ deltaNeg = 0 ∧ s.n = 0 ∧ waste = 0 := by
  have hdec := sharpness_decomposition s deltaPos deltaNeg waste hpos hneg hcarrier
  omega

/-- Conversely, zero inefficiency yields exact sharpness. -/
theorem zero_inefficiency_gives_sharpness
    (s : SharpConflictProfile)
    (hpos : s.positive = s.k)
    (hneg : s.negative = s.k)
    (hn : s.n = 0)
    (hcarrier : s.carrier = s.b) :
    s.m + s.carrier = 2 * s.k := by
  have hdec := sharpness_decomposition s 0 0 0 (by simpa using hpos)
    (by simpa using hneg) (by simpa using hcarrier)
  simpa [hn] using hdec

/-- The sharp joint FDE macrostate is unique in denominator-free form:
`T + k = m`, `F + k = m`, `m + B = 2k`, and `N = 0`.
Normalized, this is `(1-c, 2c-1, 0, 1-c)`. -/
theorem sharp_conflict_spine
    (s : SharpConflictProfile)
    (hpos : s.positive = s.k)
    (hneg : s.negative = s.k)
    (hn : s.n = 0) :
    s.t + s.k = s.m ∧
      s.f + s.k = s.m ∧
      s.m + s.b = 2 * s.k := by
  simp [positive, negative] at hpos hneg
  constructor
  · omega
  constructor <;> omega

end SharpConflictProfile

/-!
## Local topology after global sharpness

Sharpness fixes the global macrostate, but not how the carrier is distributed
among conjuncts.  For three claims, let `d` be the carrier mass and `b1,b2,b3`
the individual local-B masses.  The union bound gives `d <= b1+b2+b3`, while
each `bi <= d`.

The two extreme non-redundant realizations are:

* distributed: `(b1,b2,b3)=(d/3,d/3,d/3)` when divisible,
* concentrated: `(d,0,0)`.

Maximum redundancy is `(d,d,d)`.
The examples below witness all three shapes at the same carrier mass.
-/

structure ConflictTopology3 where
  d : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  union_le_sum : d ≤ b1 + b2 + b3
  b1_le : b1 ≤ d
  b2_le : b2 ≤ d
  b3_le : b3 ≤ d

namespace ConflictTopology3

def totalLocal (s : ConflictTopology3) : Nat := s.b1 + s.b2 + s.b3

def peak (s : ConflictTopology3) : Nat := max s.b1 (max s.b2 s.b3)

/-- Redundancy cannot exceed the concentration budget.  This is the raw-count
form of the normalized triangle inequality `r <= q`. -/
theorem total_le_three_peak (s : ConflictTopology3) :
    s.totalLocal ≤ 3 * s.peak := by
  simp [totalLocal, peak]
  have h1 : s.b1 ≤ max s.b1 (max s.b2 s.b3) := Nat.le_max_left _ _
  have h2a : s.b2 ≤ max s.b2 s.b3 := Nat.le_max_left _ _
  have h2 : s.b2 ≤ max s.b1 (max s.b2 s.b3) :=
    le_trans h2a (Nat.le_max_right _ _)
  have h3a : s.b3 ≤ max s.b2 s.b3 := Nat.le_max_right _ _
  have h3 : s.b3 ≤ max s.b1 (max s.b2 s.b3) :=
    le_trans h3a (Nat.le_max_right _ _)
  omega

/-- Distributed sharp carrier example. -/
def distributed3 : ConflictTopology3 :=
  { d := 3, b1 := 1, b2 := 1, b3 := 1
  , union_le_sum := by omega
  , b1_le := by omega, b2_le := by omega, b3_le := by omega }

/-- Concentrated sharp carrier example. -/
def concentrated3 : ConflictTopology3 :=
  { d := 3, b1 := 3, b2 := 0, b3 := 0
  , union_le_sum := by omega
  , b1_le := by omega, b2_le := by omega, b3_le := by omega }

/-- Maximally redundant sharp carrier example. -/
def redundant3 : ConflictTopology3 :=
  { d := 3, b1 := 3, b2 := 3, b3 := 3
  , union_le_sum := by omega
  , b1_le := by omega, b2_le := by omega, b3_le := by omega }

example : distributed3.totalLocal = 3 ∧ distributed3.peak = 1 := by decide
example : concentrated3.totalLocal = 3 ∧ concentrated3.peak = 3 := by decide
example : redundant3.totalLocal = 9 ∧ redundant3.peak = 3 := by decide

end ConflictTopology3

end PEL4.Paradoxes
