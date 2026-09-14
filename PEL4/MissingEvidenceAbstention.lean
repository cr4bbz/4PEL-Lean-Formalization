import PEL4.ValueOfCalibration

namespace PEL4

/-!
# Gate 82: missing evidence and rational abstention

A missing observation is not negative evidence. Gate 82 makes that distinction
operational: when the sensor channel is silent, an abstaining policy can dominate
a policy that coerces silence into a negative classification.
-/

inductive Gate82Signal where
  | positive
  | negative
  | missing
  deriving DecidableEq, Repr

inductive Gate82Verdict where
  | accept
  | reject
  | abstain
  deriving DecidableEq, Repr

/-- Unsafe completion rule: silence is coerced into rejection. -/
def gate82ForcedVerdict (signal : Gate82Signal) : Gate82Verdict :=
  match signal with
  | .positive => .accept
  | .negative => .reject
  | .missing => .reject

/-- Safe completion rule: silence remains explicitly unresolved. -/
def gate82SafeVerdict (signal : Gate82Signal) : Gate82Verdict :=
  match signal with
  | .positive => .accept
  | .negative => .reject
  | .missing => .abstain

/-- Utility witness for a genuinely positive case when the observation is lost. -/
def gate82PositiveCaseUtility (verdict : Gate82Verdict) : Rat :=
  match verdict with
  | .accept => 1
  | .abstain => (1 : Rat) / 2
  | .reject => 0

/-- Missing and negative are distinct observations at the data layer. -/
theorem gate82_missing_is_not_negative :
    Gate82Signal.missing ≠ Gate82Signal.negative := by
  decide

/-- The forced policy converts missingness into rejection. -/
theorem gate82_forced_missing_rejects :
    gate82ForcedVerdict .missing = .reject := by
  rfl

/-- The safe policy preserves missingness as abstention. -/
theorem gate82_safe_missing_abstains :
    gate82SafeVerdict .missing = .abstain := by
  rfl

/-- In the positive-case dropout witness, abstention strictly dominates forced
rejection. -/
theorem gate82_abstention_beats_forced_negative :
    gate82PositiveCaseUtility (gate82SafeVerdict .missing) >
      gate82PositiveCaseUtility (gate82ForcedVerdict .missing) := by
  native_decide

/-- Main Gate-82 theorem: absence of a signal can be preserved as epistemic
absence rather than silently converted into counterevidence. -/
theorem gate82_missing_evidence_requires_abstention :
    Gate82Signal.missing ≠ Gate82Signal.negative ∧
    gate82SafeVerdict .missing = .abstain ∧
    gate82ForcedVerdict .missing = .reject ∧
    gate82PositiveCaseUtility (gate82SafeVerdict .missing) >
      gate82PositiveCaseUtility (gate82ForcedVerdict .missing) := by
  exact ⟨gate82_missing_is_not_negative,
    gate82_safe_missing_abstains,
    gate82_forced_missing_rejects,
    gate82_abstention_beats_forced_negative⟩

/-!
## Gate-82 boundary

The utility witness fixes the hidden case as positive in order to expose the
cost of conflating missingness with negative evidence. A full decision theory of
abstention would integrate priors, asymmetric losses, and repeated sensing.
-/

end PEL4
