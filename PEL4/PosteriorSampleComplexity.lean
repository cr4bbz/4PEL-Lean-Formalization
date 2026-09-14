import PEL4.SequentialIdentifiability

namespace PEL4

/-!
# Gate 74: posterior sample complexity

Gate 66 already computed exact posterior concentration for three repeated precise
Recovery signals. Gate 74 turns those values into a finite sample-complexity
contract: for a target confidence, return the first repetition count in the
verified window `0..3` that reaches it.
-/

/-- First verified repetition count in `0..3` whose robust posterior reaches the
target. `none` means the target is not reached in the current verified window. -/
def gate74FirstHitWithinThree (target : Rat) : Option Nat :=
  if target ≤ gate66RobustMassAfterPreciseRecovery 0 then some 0
  else if target ≤ gate66RobustMassAfterPreciseRecovery 1 then some 1
  else if target ≤ gate66RobustMassAfterPreciseRecovery 2 then some 2
  else if target ≤ gate66RobustMassAfterPreciseRecovery 3 then some 3
  else none

/-- Ninety-percent posterior confidence needs one matching precise observation. -/
theorem gate74_ninety_percent_needs_one :
    gate74FirstHitWithinThree ((9 : Rat) / 10) = some 1 := by
  native_decide

/-- Ninety-eight percent needs two matching observations. -/
theorem gate74_ninety_eight_percent_needs_two :
    gate74FirstHitWithinThree ((49 : Rat) / 50) = some 2 := by
  native_decide

/-- Ninety-nine percent needs three matching observations. -/
theorem gate74_ninety_nine_percent_needs_three :
    gate74FirstHitWithinThree ((99 : Rat) / 100) = some 3 := by
  native_decide

/-- A target of 99.9% is not reached in the first three verified repetitions. -/
theorem gate74_ninety_nine_nine_not_within_three :
    gate74FirstHitWithinThree ((999 : Rat) / 1000) = none := by
  native_decide

/-- Exact posterior values underlying the sample-complexity steps. -/
theorem gate74_verified_learning_curve :
    gate66RobustMassAfterPreciseRecovery 0 = (1 : Rat) / 2 ∧
    gate66RobustMassAfterPreciseRecovery 1 = (9 : Rat) / 10 ∧
    gate66RobustMassAfterPreciseRecovery 2 = (81 : Rat) / 82 ∧
    gate66RobustMassAfterPreciseRecovery 3 = (729 : Rat) / 730 := by
  exact ⟨gate66_identifiable_mass_at_zero,
    gate66_identifiable_mass_after_one,
    gate66_identifiable_mass_after_two,
    gate66_identifiable_mass_after_three⟩

/-- Main Gate-74 theorem: stricter confidence demands more matching evidence in
the finite learning window, and sufficiently strict targets remain unreached. -/
theorem gate74_posterior_sample_complexity :
    gate74FirstHitWithinThree ((9 : Rat) / 10) = some 1 ∧
    gate74FirstHitWithinThree ((49 : Rat) / 50) = some 2 ∧
    gate74FirstHitWithinThree ((99 : Rat) / 100) = some 3 ∧
    gate74FirstHitWithinThree ((999 : Rat) / 1000) = none := by
  exact ⟨gate74_ninety_percent_needs_one,
    gate74_ninety_eight_percent_needs_two,
    gate74_ninety_nine_percent_needs_three,
    gate74_ninety_nine_nine_not_within_three⟩

/-!
## Gate-74 boundary

This is an exact finite sample-complexity witness, not a closed-form asymptotic
bound for arbitrary `epsilon`. The next gate moves in a different direction:
it introduces discounting and proves convergence of a simple infinite-horizon
Bellman iteration before attempting richer continuous belief-space results.
-/

end PEL4
