import PEL4.AdversarialSensorRobustness

namespace PEL4

/-!
# Gate 84: sensor-model identifiability

Once the agent admits that its observation model may be wrong, it needs tests
that identify the model itself. The finite witness below has four candidate
sensor configurations carrying two independent diagnostic bits.
-/

inductive Gate84SensorModel where
  | m00
  | m01
  | m10
  | m11
  deriving DecidableEq, Repr

/-- First diagnostic reads only the first latent sensor bit. -/
def gate84DiagA (model : Gate84SensorModel) : Bool :=
  match model with
  | .m00 | .m01 => false
  | .m10 | .m11 => true

/-- Second diagnostic reads only the second latent sensor bit. -/
def gate84DiagB (model : Gate84SensorModel) : Bool :=
  match model with
  | .m00 | .m10 => false
  | .m01 | .m11 => true

/-- Joint diagnostic code obtained by running both tests. -/
def gate84JointDiagnostic (model : Gate84SensorModel) : Bool × Bool :=
  (gate84DiagA model, gate84DiagB model)

/-- Diagnostic A alone aliases two distinct models. -/
theorem gate84_diagA_not_identifying :
    ∃ x y : Gate84SensorModel, x ≠ y ∧ gate84DiagA x = gate84DiagA y := by
  exact ⟨.m00, .m01, by decide, rfl⟩

/-- Diagnostic B alone also aliases two distinct models. -/
theorem gate84_diagB_not_identifying :
    ∃ x y : Gate84SensorModel, x ≠ y ∧ gate84DiagB x = gate84DiagB y := by
  exact ⟨.m00, .m10, by decide, rfl⟩

/-- Together the two diagnostics uniquely identify all four models. -/
theorem gate84_joint_diagnostic_injective :
    Function.Injective gate84JointDiagnostic := by
  intro x y h
  cases x <;> cases y <;>
    simp [gate84JointDiagnostic, gate84DiagA, gate84DiagB] at h ⊢

/-- Main Gate-84 theorem: failure of either diagnostic by itself does not imply
model non-identifiability; complementary tests can jointly identify the sensor
law. -/
theorem gate84_sequential_sensor_model_identifiability :
    (∃ x y : Gate84SensorModel, x ≠ y ∧ gate84DiagA x = gate84DiagA y) ∧
    (∃ x y : Gate84SensorModel, x ≠ y ∧ gate84DiagB x = gate84DiagB y) ∧
    Function.Injective gate84JointDiagnostic := by
  exact ⟨gate84_diagA_not_identifying,
    gate84_diagB_not_identifying,
    gate84_joint_diagnostic_injective⟩

/-!
## Gate-84 boundary

The candidate model class is finite and noiseless. The theorem isolates the
identifiability structure before later generalizations to noisy calibration,
posterior model weights, and active model discrimination.
-/

end PEL4
