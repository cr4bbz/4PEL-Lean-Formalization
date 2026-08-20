import Lean.Elab.Tactic.Omega

namespace PEL4.Paradoxes

/-- `capBudget n cap` is the total mass available in `n` coordinates if each
coordinate is bounded above by `cap`. It is written recursively so the packing
argument remains Presburger and dependency-free. -/
def capBudget : Nat → Nat → Nat
| 0, _ => 0
| n + 1, cap => cap + capBudget n cap

/-- Every coordinate in a finite error profile lies below a common cap. -/
def AllLE (cap : Nat) : List Nat → Prop
| [] => True
| x :: xs => x ≤ cap ∧ AllLE cap xs

/-- A capped finite profile cannot carry more mass than its coordinate budget. -/
theorem sum_le_capBudget
    {xs : List Nat} {cap : Nat}
    (h : AllLE cap xs) :
    xs.sum ≤ capBudget xs.length cap := by
  induction xs with
  | nil =>
      simp [capBudget]
  | cons x xs ih =>
      simp [AllLE] at h
      rcases h with ⟨hx, hxs⟩
      have htail := ih hxs
      simp [capBudget]
      omega

/--
An arbitrary one-error Preface family.

`a` is the all-correct mass. `errors` contains one mutually exclusive error mass
for each claim. The total finite mass is `m`, and `k/m` is the Lockean threshold.
-/
structure PrefacePacking where
  a : Nat
  errors : List Nat
  m : Nat
  k : Nat
  total : a + errors.sum = m

/--
The one-error Preface region: global fallibility is accepted (`a ≤ m-k`) and
every individual claim is accepted (each corresponding error mass is ≤ `m-k`).
-/
def PrefacePacking.InRegion (s : PrefacePacking) : Prop :=
  s.a ≤ s.m - s.k ∧ AllLE (s.m - s.k) s.errors

/--
General simplex packing theorem.

If a one-error Preface state exists, then the total mass must fit inside
`n+1` coordinates, each capped at `m-k`, where `n` is the number of claims.
This is the exact combinatorial content behind the geometric boundary
`c ≤ n/(n+1)`.
-/
theorem preface_general_packing_bound
    (s : PrefacePacking)
    (h : s.InRegion) :
    s.m ≤ capBudget (s.errors.length + 1) (s.m - s.k) := by
  rcases h with ⟨ha, herr⟩
  have hsum := sum_le_capBudget herr
  simp [capBudget]
  omega

/-- Fixed-`n` form of the general packing theorem. -/
theorem preface_n_claim_packing_bound
    (s : PrefacePacking)
    (n : Nat)
    (hlen : s.errors.length = n)
    (h : s.InRegion) :
    s.m ≤ capBudget (n + 1) (s.m - s.k) := by
  simpa [hlen] using preface_general_packing_bound s h

/-- The three-claim theorem specializes to four capped coordinates. -/
example
    (s : PrefacePacking)
    (hlen : s.errors.length = 3)
    (h : s.InRegion) :
    s.m ≤ 4 * (s.m - s.k) := by
  have hp := preface_n_claim_packing_bound s 3 hlen h
  simpa [capBudget, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hp

end PEL4.Paradoxes
