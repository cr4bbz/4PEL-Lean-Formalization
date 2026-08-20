namespace PEL4.Paradoxes

/--
A denominator-free encoding of the symmetric Preface threshold region.

For `n` representative claims we use `n + 1` equiprobable worlds:
one all-correct world and one one-error world for each claim.
A Lockean threshold `k / (n + 1)` is admissible exactly when it is a strict
majority (`2*k > n+1`) and every individual claim still reaches it (`k ≤ n`).
-/
def SymmetricPrefaceRegion (n k : Nat) : Prop :=
  2 * k > n + 1 ∧ k ≤ n

/-- Every individual claim has support count `n` in the symmetric model. -/
def SymmetricLocalAccepted (n k : Nat) : Prop := k ≤ n

/-- The conjunction has support count exactly `1`. -/
def SymmetricConjunctionRejected (k : Nat) : Prop := 1 < k

/-- "At least one claim is wrong" has support count exactly `n`. -/
def SymmetricFallibilityAccepted (n k : Nat) : Prop := k ≤ n

/--
Threshold-boundary theorem for the symmetric Preface family.

Once there are at least two claims, every strict-majority threshold that does
not exceed the local support count yields all three characteristic features:
local acceptance, rejection of the total conjunction, and acceptance of
fallibility.
-/
theorem symmetric_preface_boundary
    {n k : Nat}
    (hn : 2 ≤ n)
    (hregion : SymmetricPrefaceRegion n k) :
    SymmetricLocalAccepted n k ∧
      SymmetricConjunctionRejected k ∧
      SymmetricFallibilityAccepted n k := by
  rcases hregion with ⟨hmajority, hlocal⟩
  constructor
  · exact hlocal
  constructor
  · omega
  · exact hlocal

/--
The symmetric Preface region is non-empty exactly from two claims onward.
Thus the aggregation phenomenon is structural rather than a peculiarity of the
three-claim control model.
-/
theorem symmetric_preface_region_nonempty_iff (n : Nat) :
    (∃ k, SymmetricPrefaceRegion n k) ↔ 2 ≤ n := by
  constructor
  · rintro ⟨k, hmajority, hlocal⟩
    omega
  · intro hn
    refine ⟨n, ?_, le_rfl⟩
    omega

/-- The three-claim example sits at the upper boundary `k = n = 3`. -/
example : SymmetricPrefaceRegion 3 3 := by
  omega

/-- A two-claim Preface model already exists at threshold `2/3`. -/
example : SymmetricPrefaceRegion 2 2 := by
  omega

end PEL4.Paradoxes
