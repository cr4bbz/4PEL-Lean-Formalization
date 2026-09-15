import PEL4.ActiveIdentificationRepair

namespace PEL4

/-!
# Gate 112: cost of identifiability

Gate 111 showed that an active diagnostic can break an observational alias and
restore truth-guaranteeing repair. Gate 112 asks when paying for that diagnostic
is decision-rational.

The witness keeps Gate 110's two equiprobable hidden worlds. A blind classical
commitment is correct in one of the two worlds, hence has expected value `1/2`.
The Gate-111 disambiguating experiment identifies the world perfectly, so its
gross value is `1`; after a diagnostic cost `c`, its net value is `1 - c`.
This yields an exact break-even cost of `1/2`.
-/

inductive Gate112Action where
  | commitPositive
  | disambiguate
  deriving DecidableEq, Repr

/-- Under a symmetric prior over Gate-110's two hidden worlds, any blind strict
commitment is correct with probability `1/2`. -/
def gate112BlindCommitValue : Rat := (1 : Rat) / 2

/-- Gate 111's perfect separating diagnostic yields a correct strict verdict in
both hidden worlds, hence gross value `1`. -/
def gate112DiagnosticGrossValue : Rat := 1

/-- Net value of buying identifiability at cost `cost`. -/
def gate112DiagnosticNetValue (cost : Rat) : Rat :=
  gate112DiagnosticGrossValue - cost

/-- Ties go to the blind commitment, so identifiability is purchased only when it
strictly improves expected value. -/
def gate112ChooseAction (cost : Rat) : Gate112Action :=
  if gate112DiagnosticNetValue cost > gate112BlindCommitValue then
    .disambiguate
  else
    .commitPositive

/-- Exact cost threshold for active identification. -/
theorem gate112_identifiability_threshold (cost : Rat) :
    gate112DiagnosticNetValue cost > gate112BlindCommitValue ↔
      cost < (1 : Rat) / 2 := by
  unfold gate112DiagnosticNetValue gate112DiagnosticGrossValue gate112BlindCommitValue
  change ((1 : Rat) / 2 < 1 - cost) ↔ cost < (1 : Rat) / 2
  rw [Rat.lt_sub_right_iff_add_lt]
  have hsum : (1 : Rat) / 2 + (1 : Rat) / 2 = 1 := by
    native_decide
  constructor
  · intro h
    have h' :
        (1 : Rat) / 2 + cost < (1 : Rat) / 2 + (1 : Rat) / 2 := by
      simpa [hsum] using h
    exact (Rat.add_lt_add_left).mp h'
  · intro h
    have h' :
        (1 : Rat) / 2 + cost < (1 : Rat) / 2 + (1 : Rat) / 2 :=
      (Rat.add_lt_add_left).mpr h
    simpa [hsum] using h'

/-- A cheap separating diagnostic is worth buying. -/
def gate112LowCost : Rat := (1 : Rat) / 4

/-- An expensive separating diagnostic is not worth buying in this witness. -/
def gate112HighCost : Rat := (3 : Rat) / 4

theorem gate112_low_cost_buys_identifiability :
    gate112ChooseAction gate112LowCost = .disambiguate := by
  native_decide

theorem gate112_high_cost_declines_identifiability :
    gate112ChooseAction gate112HighCost = .commitPositive := by
  native_decide

/-- The diagnostic whose value is priced here is genuinely truth-guaranteeing by
Gate 111. -/
theorem gate112_priced_experiment_is_truth_guaranteeing :
    Gate111TruthGuaranteeing .disambiguate :=
  gate111_diagnostic_truth_guaranteeing

/-- Main Gate-112 result: access to a truth-guaranteeing experiment does not imply
that a value-maximizing agent should always buy it. In this finite symmetric
witness, the exact break-even price of identifiability is `1/2`. -/
theorem gate112_cost_of_identifiability :
    (∀ cost : Rat,
      gate112DiagnosticNetValue cost > gate112BlindCommitValue ↔
        cost < (1 : Rat) / 2) ∧
    gate112ChooseAction gate112LowCost = .disambiguate ∧
    gate112ChooseAction gate112HighCost = .commitPositive ∧
    Gate111TruthGuaranteeing .disambiguate := by
  exact ⟨gate112_identifiability_threshold,
    gate112_low_cost_buys_identifiability,
    gate112_high_cost_declines_identifiability,
    gate111_diagnostic_truth_guaranteeing⟩

/-!
## Gate-112 interpretation boundary

The value model is intentionally simple: symmetric prior, unit reward for a
correct strict verdict, zero for a wrong verdict, and a perfectly separating
diagnostic. The numerical threshold `1/2` is therefore witness-specific.

The structural result is the important part: identifiability has an opportunity
cost, so the existence of an alias-breaking intervention does not by itself make
using it rational. Gate 113 adds a third option that Gate 112 deliberately omits:
remaining unresolved at `N` rather than buying information or making a blind
classical commitment.
-/

end PEL4
