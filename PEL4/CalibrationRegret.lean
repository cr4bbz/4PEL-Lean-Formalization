import PEL4.SelfCorrectingPolicy

namespace PEL4

/-!
# Gate 96: calibration regret
-/

def gate96TrueBestValue : Rat := gate78ProbeValue .degraded .safe

def gate96RealizedValue (belief : Gate86ModelBelief) : Rat :=
  gate78ProbeValue .degraded (gate86ChooseProbe belief)

def gate96Regret (belief : Gate86ModelBelief) : Rat :=
  gate96TrueBestValue - gate96RealizedValue belief

theorem gate96_true_best_value :
    gate96TrueBestValue = (3 : Rat) / 5 := by
  native_decide

theorem gate96_precalibration_regret :
    gate96Regret gate95OverconfidentBelief = (1 : Rat) / 2 := by
  native_decide

theorem gate96_postcalibration_regret_zero :
    gate96Regret gate95CorrectedBelief = 0 := by
  native_decide

theorem gate96_calibration_strictly_reduces_regret :
    gate96Regret gate95CorrectedBelief < gate96Regret gate95OverconfidentBelief := by
  native_decide

theorem gate96_calibration_eliminates_realized_regret :
    gate96Regret gate95OverconfidentBelief = (1 : Rat) / 2 ∧
    gate96Regret gate95CorrectedBelief = 0 ∧
    gate96Regret gate95CorrectedBelief < gate96Regret gate95OverconfidentBelief := by
  exact ⟨gate96_precalibration_regret,
    gate96_postcalibration_regret_zero,
    gate96_calibration_strictly_reduces_regret⟩

end PEL4
