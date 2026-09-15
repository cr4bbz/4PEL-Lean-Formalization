import PEL4.CostOfIdentifiability

namespace PEL4

/-!
# Gate 113: rational unresolvedness

Gate 112 priced a perfect alias-breaking diagnostic against a blind classical
commitment. Gate 113 adds a third epistemic option: remain deliberately unresolved
rather than force a strict `T/F` verdict.

The witness assigns safe deferral value `3/5`. This exceeds the `1/2` expected
value of a blind strict commitment under the symmetric Gate-110 prior, but remains
below the gross value `1` of perfect identification. Consequently, cheap
identification is purchased while sufficiently expensive identification makes
continued `N` value-optimal.
-/

inductive Gate113Action where
  | commitPositive
  | commitNegative
  | remainUnresolved
  | disambiguate
  deriving DecidableEq, Repr

/-- Value of postponing a strict verdict while retaining the epistemic gap. -/
def gate113UnresolvedValue : Rat := (3 : Rat) / 5

/-- Blind strict commitment inherits Gate 112's symmetric value. -/
def gate113BlindCommitValue : Rat := gate112BlindCommitValue

/-- Buying perfect identification inherits Gate 112's cost-parametric value. -/
def gate113DiagnosticNetValue (cost : Rat) : Rat :=
  gate112DiagnosticNetValue cost

/-- Since blind commitments are dominated by safe unresolvedness in this witness,
the live choice is between paying for identification and retaining `N`. Ties
remain unresolved. -/
def gate113ChooseAction (cost : Rat) : Gate113Action :=
  if gate113DiagnosticNetValue cost > gate113UnresolvedValue then
    .disambiguate
  else
    .remainUnresolved

/-- Remaining unresolved strictly dominates a blind classical commitment. -/
theorem gate113_unresolved_beats_blind_commitment :
    gate113UnresolvedValue > gate113BlindCommitValue := by
  native_decide

/-- Exact price threshold against rational unresolvedness: perfect identification
beats safe deferral exactly below cost `2/5`. -/
theorem gate113_identification_vs_unresolved_threshold (cost : Rat) :
    gate113DiagnosticNetValue cost > gate113UnresolvedValue ↔
      cost < (2 : Rat) / 5 := by
  unfold gate113DiagnosticNetValue gate113UnresolvedValue
  unfold gate112DiagnosticNetValue gate112DiagnosticGrossValue
  change ((3 : Rat) / 5 < 1 - cost) ↔ cost < (2 : Rat) / 5
  rw [Rat.lt_sub_right_iff_add_lt]
  have hsum : (3 : Rat) / 5 + (2 : Rat) / 5 = 1 := by
    native_decide
  constructor
  · intro h
    have h' :
        (3 : Rat) / 5 + cost < (3 : Rat) / 5 + (2 : Rat) / 5 := by
      simpa [hsum] using h
    exact (Rat.add_lt_add_left).mp h'
  · intro h
    have h' :
        (3 : Rat) / 5 + cost < (3 : Rat) / 5 + (2 : Rat) / 5 :=
      (Rat.add_lt_add_left).mpr h
    simpa [hsum] using h'

/-- Cheap identification still wins. -/
def gate113LowCost : Rat := (1 : Rat) / 4

/-- At this higher cost, safe unresolvedness is preferable. -/
def gate113HighCost : Rat := (1 : Rat) / 2

theorem gate113_low_cost_identifies :
    gate113ChooseAction gate113LowCost = .disambiguate := by
  native_decide

theorem gate113_high_cost_remains_unresolved :
    gate113ChooseAction gate113HighCost = .remainUnresolved := by
  native_decide

/-- The unresolved option corresponds to the visible Gate-110 world gap: the
first-order coordinate remains `N` while model trust remains strict `T`. -/
theorem gate113_unresolved_state_is_N_under_trusted_model :
    (gate110VisibleState Gate110HiddenWorld.positive).world = FDEValue.N ∧
    (gate110VisibleState Gate110HiddenWorld.positive).model = FDEValue.T := by
  native_decide

/-- Main Gate-113 result: when blind classicalization is worse than safe deferral
and perfect identification is too expensive, preserving a genuine four-valued gap
is value-optimal in the explicit finite witness. -/
theorem gate113_rational_unresolvedness :
    gate113UnresolvedValue > gate113BlindCommitValue ∧
    (∀ cost : Rat,
      gate113DiagnosticNetValue cost > gate113UnresolvedValue ↔
        cost < (2 : Rat) / 5) ∧
    gate113ChooseAction gate113LowCost = .disambiguate ∧
    gate113ChooseAction gate113HighCost = .remainUnresolved ∧
    (gate110VisibleState Gate110HiddenWorld.positive).world = FDEValue.N := by
  exact ⟨gate113_unresolved_beats_blind_commitment,
    gate113_identification_vs_unresolved_threshold,
    gate113_low_cost_identifies,
    gate113_high_cost_remains_unresolved,
    gate113_unresolved_state_is_N_under_trusted_model.1⟩

/-!
## Gate-113 interpretation boundary

The value `3/5` assigned to safe deferral is an explicit modelling choice, not a
universal utility of ignorance. Gate 113 therefore does not claim that `N` is
always preferable to action or inquiry.

What is established is structural: once unresolvedness is admitted as a genuine
control option, there are coherent finite value models in which rational agency
preserves `N` rather than either buying expensive information or manufacturing a
classical verdict unsupported by the available evidence.

Gate 114 now removes the numerical witness and asks for the abstract condition
under which any truth-guaranteeing decoder can exist at all.
-/

end PEL4
