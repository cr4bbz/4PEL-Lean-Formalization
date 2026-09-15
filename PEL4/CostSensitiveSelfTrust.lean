import PEL4.NestedStateReachability
import PEL4.ActiveCalibration

namespace PEL4

/-!
# Gate 106: cost-sensitive epistemic self-trust

Gate 104 assigns epistemic-maintenance actions directly from four-valued status:
for example, model status `N` triggers calibration. Gate 106 asks whether that
priority can instead be justified by decision value.

We reuse the exact finite decision problem from Gate 92, but expose calibration
cost as a parameter. This turns the formerly fixed action into a threshold
question: when is the expected benefit of self-calibration worth paying for?
-/

/-- Net value of calibration when its cost is made explicit. -/
def gate106CalibrationNetValue (cost : Rat) : Rat :=
  gate92CalibrationGrossValue - cost

/-- Cost-parametric version of the Gate-92 controller. -/
def gate106ChooseAction (cost : Rat) : Gate92Action :=
  if gate106CalibrationNetValue cost > gate92WorldSenseNetValue then
    if gate106CalibrationNetValue cost > gate92ActNowValue then
      .calibrateModel
    else
      .actNow
  else if gate92WorldSenseNetValue > gate92ActNowValue then
    .senseWorld
  else
    .actNow

/-- The strongest non-calibration option in this witness is first-order sensing. -/
theorem gate106_world_sensing_beats_acting_now :
    gate92WorldSenseNetValue > gate92ActNowValue := by
  native_decide

/-- Exact break-even threshold against the best non-calibration option.
Calibration beats world sensing exactly when its cost is below `13/200`. -/
theorem gate106_calibration_threshold (cost : Rat) :
    gate106CalibrationNetValue cost > gate92WorldSenseNetValue ↔
      cost < (13 : Rat) / 200 := by
  unfold gate106CalibrationNetValue
  rw [gate92_calibration_gross_value]
  unfold gate92WorldSenseNetValue
  rw [Rat.lt_sub_right_iff_add_lt]
  have hsum : (31 : Rat) / 50 + (13 : Rat) / 200 = (137 : Rat) / 200 := by
    native_decide
  rw [← hsum]
  exact Rat.add_lt_add_left

/-- Against acting immediately, the corresponding break-even cost is `17/200`.
The tighter `13/200` threshold therefore comes from the availability of world
sensing as an alternative. -/
theorem gate106_calibration_vs_act_threshold (cost : Rat) :
    gate106CalibrationNetValue cost > gate92ActNowValue ↔
      cost < (17 : Rat) / 200 := by
  unfold gate106CalibrationNetValue
  rw [gate92_calibration_gross_value, gate92_act_now_value]
  rw [Rat.lt_sub_right_iff_add_lt]
  have hsum : (3 : Rat) / 5 + (17 : Rat) / 200 = (137 : Rat) / 200 := by
    native_decide
  rw [← hsum]
  exact Rat.add_lt_add_left

/-- The original Gate-92 calibration cost lies below the derived threshold. -/
def gate106LowCalibrationCost : Rat := (1 : Rat) / 20

/-- A higher calibration cost that lies above the threshold. -/
def gate106HighCalibrationCost : Rat := (1 : Rat) / 10

theorem gate106_low_cost_calibrates :
    gate106ChooseAction gate106LowCalibrationCost = .calibrateModel := by
  native_decide

theorem gate106_high_cost_senses_world :
    gate106ChooseAction gate106HighCalibrationCost = .senseWorld := by
  native_decide

/-- Gate 104 treats the model gap as sufficient to select calibration, whereas
Gate 106 demonstrates that the same epistemic situation can rationally select a
different action once calibration cost changes. -/
theorem gate106_status_alone_does_not_fix_action :
    gate103TruthWithModelGap.model = FDEValue.N ∧
    gate104ChooseAction gate103TruthWithModelGap = Gate104Action.calibrateModel ∧
    gate106ChooseAction gate106LowCalibrationCost = Gate92Action.calibrateModel ∧
    gate106ChooseAction gate106HighCalibrationCost = Gate92Action.senseWorld := by
  native_decide

/-- The derived threshold itself changes the optimal policy on the two concrete
sides of the boundary. -/
theorem gate106_cost_crosses_policy_boundary :
    gate106LowCalibrationCost < (13 : Rat) / 200 ∧
    ¬ gate106HighCalibrationCost < (13 : Rat) / 200 ∧
    gate106ChooseAction gate106LowCalibrationCost = .calibrateModel ∧
    gate106ChooseAction gate106HighCalibrationCost = .senseWorld := by
  native_decide

/-- Main Gate-106 result: the unconditional Gate-104 maintenance priority is a
valid policy witness, but it is not forced by four-valued status alone. In the
same finite decision problem, a cost threshold determines whether self-calibration
or further world sensing has greater expected value. -/
theorem gate106_cost_sensitive_self_trust :
    (∀ cost : Rat,
      gate106CalibrationNetValue cost > gate92WorldSenseNetValue ↔
        cost < (13 : Rat) / 200) ∧
    gate106ChooseAction gate106LowCalibrationCost = .calibrateModel ∧
    gate106ChooseAction gate106HighCalibrationCost = .senseWorld := by
  exact ⟨gate106_calibration_threshold,
    gate106_low_cost_calibrates,
    gate106_high_cost_senses_world⟩

/-!
## Gate-106 interpretation boundary

Gate 106 derives a genuine cost threshold, but only inside the concrete finite
value model inherited from Gate 92. It does not prove that `13/200` is universal,
nor that expected-value maximization is the only norm of rational self-trust.
What is established is more structural: a four-valued model verdict by itself is
insufficient to determine the value-optimal maintenance action once epistemic
actions have nontrivial costs.

Gate 107 will push this one level deeper by asking whether even the complete
nested pair `(worldStatus, modelStatus)` preserves enough quantitative information
for optimal control.
-/

end PEL4
