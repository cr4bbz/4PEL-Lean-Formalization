import Lean.Elab.Tactic.Omega
import PEL4.Paradoxes.PrefacePacking
import PEL4.Paradoxes.PrefaceSharpness

namespace PEL4.Paradoxes

/-!
# N-claim latent-conflict topology

`PrefaceSharpness.lean` showed for three claims that a sharp global conflict
still leaves freedom in the way local B-mass is organized.  This module lifts
the raw geometry to an arbitrary finite list of conjuncts.

Let

* `d` be the mass of the union of all local glut carriers,
* `b_i` be the local glut mass of conjunct `i`,
* `S = sum_i b_i`,
* `p = max_i b_i`,
* `n` be the number of conjuncts.

Then the topology satisfies the dimension-independent chain

  d <= S <= n*p <= n*d.

After subtracting `d` and normalizing by `(n-1)d`, this is the raw content of

  0 <= r <= q <= 1,

where `q` measures concentration and `r` measures redundancy.
-/

/-- Maximum of a finite list of natural-number masses. -/
def maxNatList : List Nat → Nat
| [] => 0
| x :: xs => max x (maxNatList xs)

/-- Raising a common cap preserves `AllLE`. -/
theorem allLE_mono {a b : Nat} (hab : a ≤ b) :
    ∀ xs : List Nat, AllLE a xs → AllLE b xs
| [], _ => by simp [AllLE]
| x :: xs, h => by
    change x ≤ a ∧ AllLE a xs at h
    change x ≤ b ∧ AllLE b xs
    exact ⟨Nat.le_trans h.1 hab, allLE_mono hab xs h.2⟩

/-- Every entry is bounded by the maximum of its list. -/
theorem allLE_maxNatList :
    ∀ xs : List Nat, AllLE (maxNatList xs) xs
| [] => by simp [AllLE]
| x :: xs => by
    change x ≤ max x (maxNatList xs) ∧ AllLE (max x (maxNatList xs)) xs
    constructor
    · exact Nat.le_max_left _ _
    · exact allLE_mono (Nat.le_max_right x (maxNatList xs)) xs
        (allLE_maxNatList xs)

/-- If every entry lies below `d`, then the list maximum also lies below `d`. -/
theorem maxNatList_le_of_allLE (d : Nat) :
    ∀ xs : List Nat, AllLE d xs → maxNatList xs ≤ d
| [], _ => by simp [maxNatList]
| x :: xs, h => by
    change x ≤ d ∧ AllLE d xs at h
    change max x (maxNatList xs) ≤ d
    exact Nat.max_le_of_le_of_le h.1 (maxNatList_le_of_allLE d xs h.2)

/-- Recursive cap budget is ordinary multiplication. -/
theorem capBudget_eq_mul (n cap : Nat) :
    capBudget n cap = n * cap := by
  induction n with
  | zero => simp [capBudget]
  | succ n ih =>
      simp [capBudget, ih, Nat.succ_mul, Nat.add_comm]

/-- Saturating a common coordinate cap forces every entry to equal that cap. -/
theorem allLE_sum_eq_budget_eq_replicate (cap : Nat) :
    ∀ xs : List Nat,
      AllLE cap xs →
      xs.sum = capBudget xs.length cap →
      xs = List.replicate xs.length cap
| [], _, _ => by simp
| x :: xs, hle, hsum => by
    change x ≤ cap ∧ AllLE cap xs at hle
    rcases hle with ⟨hx, hxs⟩
    have htailLe := sum_le_capBudget hxs
    change x + xs.sum = cap + capBudget xs.length cap at hsum
    have hxEq : x = cap := by omega
    have htailEq : xs.sum = capBudget xs.length cap := by omega
    have ih := allLE_sum_eq_budget_eq_replicate cap xs hxs htailEq
    rw [hxEq]
    change cap :: xs = cap :: List.replicate xs.length cap
    exact congrArg (fun ys => cap :: ys) ih

/-- An n-claim conflict topology represented only by its carrier mass and
individual local glut masses.  The first inequality is the union bound; the
second field records that every local glut set lies inside the carrier union. -/
structure ConflictTopologyN where
  d : Nat
  masses : List Nat
  union_le_sum : d ≤ masses.sum
  local_le_carrier : AllLE d masses

namespace ConflictTopologyN

/-- Number of conjuncts. -/
def arity (s : ConflictTopologyN) : Nat := s.masses.length

/-- Sum of all local glut masses. -/
def totalLocal (s : ConflictTopologyN) : Nat := s.masses.sum

/-- Largest local glut mass. -/
def peak (s : ConflictTopologyN) : Nat := maxNatList s.masses

/-- The local masses fit below `n * peak`. -/
theorem total_le_n_peak (s : ConflictTopologyN) :
    s.totalLocal ≤ s.arity * s.peak := by
  have h := sum_le_capBudget (allLE_maxNatList s.masses)
  simpa [totalLocal, arity, peak, capBudget_eq_mul] using h

/-- No individual local glut mass can exceed the carrier union. -/
theorem peak_le_carrier (s : ConflictTopologyN) :
    s.peak ≤ s.d := by
  exact maxNatList_le_of_allLE s.d s.masses s.local_le_carrier

/-- General raw latent-conflict triangle chain.

  d <= S <= n*p <= n*d

This is denominator-free and remains valid for every finite arity. -/
theorem raw_triangle_chain (s : ConflictTopologyN) :
    s.d ≤ s.totalLocal ∧
      s.totalLocal ≤ s.arity * s.peak ∧
      s.arity * s.peak ≤ s.arity * s.d := by
  constructor
  · exact s.union_le_sum
  constructor
  · exact total_le_n_peak s
  · exact Nat.mul_le_mul_left s.arity (peak_le_carrier s)

/-- Pigeonhole form: the carrier mass cannot exceed `n * peak`.
Normalized, at least one conjunct carries at least a `1/n` share of the union
mass. -/
theorem carrier_le_n_peak (s : ConflictTopologyN) :
    s.d ≤ s.arity * s.peak := by
  have h := raw_triangle_chain s
  exact Nat.le_trans h.1 h.2.1

/-- Total redundancy is at most `n` copies of the carrier mass. -/
theorem total_le_n_carrier (s : ConflictTopologyN) :
    s.totalLocal ≤ s.arity * s.d := by
  have h := raw_triangle_chain s
  exact Nat.le_trans h.2.1 h.2.2

/-- Raw numerator inequality behind `r <= q`:

  S - d <= n*p - d.
-/
theorem redundancy_numerator_le_concentration_numerator
    (s : ConflictTopologyN) :
    s.totalLocal - s.d ≤ s.arity * s.peak - s.d := by
  exact Nat.sub_le_sub_right (total_le_n_peak s) s.d

/-- Raw upper bound behind `q <= 1`. -/
theorem concentration_product_le_full_carrier_budget
    (s : ConflictTopologyN) :
    s.arity * s.peak ≤ s.arity * s.d :=
  Nat.mul_le_mul_left s.arity (peak_le_carrier s)

/-- If the carrier saturates the pigeonhole bound, then the total local mass is
forced to the same value.  Thus exact minimum concentration also eliminates
redundancy at the count level. -/
theorem minimal_peak_forces_no_redundancy
    (s : ConflictTopologyN)
    (hsat : s.arity * s.peak = s.d) :
    s.totalLocal = s.d := by
  have hlower : s.d ≤ s.totalLocal := by
    simpa [totalLocal] using s.union_le_sum
  have hupper := total_le_n_peak s
  omega

/-- Equality on the triangle diagonal `S = n*p` forces every local marginal to
reach the same peak.  Thus `r = q` means equal conflict loads, not merely a
numerical coincidence. -/
theorem diagonal_forces_equal_local_masses
    (s : ConflictTopologyN)
    (hdiag : s.totalLocal = s.arity * s.peak) :
    s.masses = List.replicate s.arity s.peak := by
  have hle := allLE_maxNatList s.masses
  have hbudget : s.masses.sum = capBudget s.masses.length s.peak := by
    simpa [totalLocal, arity, peak, capBudget_eq_mul] using hdiag
  exact allLE_sum_eq_budget_eq_replicate s.peak s.masses hle hbudget

/-- Maximum redundancy `S = n*d` forces every local glut marginal to equal the
entire carrier mass. -/
theorem maximal_redundancy_forces_full_carrier_marginals
    (s : ConflictTopologyN)
    (hfull : s.totalLocal = s.arity * s.d) :
    s.masses = List.replicate s.arity s.d := by
  have hbudget : s.masses.sum = capBudget s.masses.length s.d := by
    simpa [totalLocal, arity, capBudget_eq_mul] using hfull
  exact allLE_sum_eq_budget_eq_replicate s.d s.masses s.local_le_carrier hbudget

/-- Three-claim examples recover the old triangle corners in the generic
representation. -/
def distributed3N : ConflictTopologyN :=
  { d := 3
  , masses := [1, 1, 1]
  , union_le_sum := by decide
  , local_le_carrier := by simp [AllLE] }

/-- One conjunct carries the whole conflict region. -/
def concentrated3N : ConflictTopologyN :=
  { d := 3
  , masses := [3, 0, 0]
  , union_le_sum := by decide
  , local_le_carrier := by simp [AllLE] }

/-- Every conjunct is glutty throughout the full carrier region. -/
def redundant3N : ConflictTopologyN :=
  { d := 3
  , masses := [3, 3, 3]
  , union_le_sum := by decide
  , local_le_carrier := by simp [AllLE] }

example : distributed3N.totalLocal = 3 ∧ distributed3N.peak = 1 := by
  constructor <;> rfl
example : concentrated3N.totalLocal = 3 ∧ concentrated3N.peak = 3 := by
  constructor <;> rfl
example : redundant3N.totalLocal = 9 ∧ redundant3N.peak = 3 := by
  constructor <;> rfl

end ConflictTopologyN

end PEL4.Paradoxes
