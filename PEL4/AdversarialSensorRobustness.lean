import PEL4.MissingEvidenceAbstention

namespace PEL4

/-!
# Gate 83: adversarial sensor robustness

Model uncertainty may be accidental, but an evidence channel can also be
systematically corrupted. Gate 83 compares a high-ceiling fragile sensor with a
lower-ceiling hardened sensor under normal and attacked regimes.
-/

inductive Gate83Regime where
  | normal
  | attacked
  deriving DecidableEq, Repr

inductive Gate83Sensor where
  | fragile
  | hardened
  deriving DecidableEq, Repr

/-- Utility of each sensor under normal and attacked operation. -/
def gate83SensorValue (regime : Gate83Regime) (sensor : Gate83Sensor) : Rat :=
  match regime, sensor with
  | .normal, .fragile => (9 : Rat) / 10
  | .attacked, .fragile => 0
  | _, .hardened => (7 : Rat) / 10

/-- Nominal operation favors the fragile high-ceiling sensor. -/
theorem gate83_normal_prefers_fragile :
    gate83SensorValue .normal .fragile > gate83SensorValue .normal .hardened := by
  native_decide

/-- Under attack the hardened sensor strictly dominates. -/
theorem gate83_attack_prefers_hardened :
    gate83SensorValue .attacked .hardened > gate83SensorValue .attacked .fragile := by
  native_decide

/-- Explicit worst-case guarantee of each sensor. -/
def gate83WorstCase (sensor : Gate83Sensor) : Rat :=
  match sensor with
  | .fragile => 0
  | .hardened => (7 : Rat) / 10

inductive Gate83PolicyChoice where
  | chooseFragile
  | chooseHardened
  deriving DecidableEq, Repr

/-- Robust policy maximizes the guaranteed value. -/
def gate83RobustChoice : Gate83PolicyChoice :=
  if gate83WorstCase .hardened > gate83WorstCase .fragile then
    .chooseHardened
  else
    .chooseFragile

/-- The robust policy selects the hardened channel. -/
theorem gate83_robust_choice_hardened :
    gate83RobustChoice = .chooseHardened := by
  native_decide

/-- Main Gate-83 theorem: robustness to possible corruption can justify a sensor
with a lower nominal ceiling but a strictly better worst-case guarantee. -/
theorem gate83_adversarial_robustness :
    gate83SensorValue .normal .fragile > gate83SensorValue .normal .hardened ∧
    gate83SensorValue .attacked .hardened > gate83SensorValue .attacked .fragile ∧
    gate83WorstCase .hardened > gate83WorstCase .fragile ∧
    gate83RobustChoice = .chooseHardened := by
  exact ⟨gate83_normal_prefers_fragile,
    gate83_attack_prefers_hardened,
    by native_decide,
    gate83_robust_choice_hardened⟩

/-!
## Gate-83 boundary

The attack is represented as an extreme finite regime rather than a strategic
game against an adversary. The result isolates the robust-control phenomenon
needed before introducing richer contamination or Byzantine observation models.
-/

end PEL4
