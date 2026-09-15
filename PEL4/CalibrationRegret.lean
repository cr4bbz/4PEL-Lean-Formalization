import PEL4.SelfCorrectingPolicy

namespace PEL4

/-!
# Gate 96: calibration regret

Gate 95 showed that calibration can repair a genuinely wrong action. Gate 96
quantifies the decision loss before and after that repair under the true degraded
sensor model.
-/

/-- Objective best value when the true sensor model is degraded. -/
def gate96TrueBestValue : Rat := gate78ProbeValue .degraded .safe

/-- Realized value of the policy induced by a model belief. -/
def gate96RealizedValue (belief : Gate86ModelBelief) : Rat :=
  gate78ProbeValue .degraded (gate86ChooseProbe belief)

/-- Regret relative to the true best degraded-model action. -/
def gate96Regret (belief : Gate86ModelBelief) : Rat :=
  gate96TrueBestValue - gate96RealizedValue belief

theorem gate96_true_best_value :
    gate96TrueBestValue = (3 : Rat) / 5 := by
  native_decide

/-- Overconfidence pays the full `1/2` value penalty. -/
theorem gate96_precalibration_regret :
    gate96Regret gate95OverconfidentBelief = (1 : Rat) / 2 := by
  native_decide

/-- After a failed calibration corrects the model belief, realized regret is zero. -/
theorem gate96_postcalibration_regret_zero :
    gate96Regret gate95CorrectedBelief = 0 := by
  native_decide

/-- Calibration strictly reduces realized decision regret in the witness. -/
theorem gate96_calibration_strictly_reduces_regret :
    gate96Regret gate95CorrectedBelief < gate96Regret gate95OverconfidentBelief := by
  native_decide

/-- Main Gate-96 theorem: the self-correcting policy from Gate 95 eliminates the
entire realized action regret under the true degraded model. -/
theorem gate96_calibration_eliminates_realized_regret :
    gate96Regret gate95OverconfidentBelief = (1 : Rat) / 2 ∧
    gate96Regret gate95CorrectedBelief = 0 ∧
    gate96Regret gate95CorrectedBelief < gate96Regret gate95OverconfidentBelief := by
  exact ⟨gate96_precalibration_regret,
    gate96_postcalibration_regret_zero,
    gate96_calibration_strictly_reduces_regret⟩

/-!
## Boundary

The true degraded model is fixed externally for this finite witness. Gate 96 does
not claim that every calibration observation reduces regret ex ante.
-/

end PEL4
