import PEL4.NestedFourValuedEpistemics
import PEL4.AnomalyDrivenModelExpansion

namespace PEL4

/-!
# Gate 104: rational epistemic self-trust

Gate 103 separated first-order world status from second-order model status.
Gate 104 turns that product state into a control policy. The agent acts directly
on the world only when its epistemic model is strictly supported. A gap, glut, or
negative model verdict triggers epistemic maintenance before world-directed action.
-/

inductive Gate104Action where
  | actPositive
  | actNegative
  | senseWorld
  | calibrateModel
  | reconcileModel
  deriving DecidableEq, Repr

/-- A finite self-trust controller over the two four-valued coordinates.

Priority is deliberately second-order:
* model `N` or `F` -> calibrate the epistemic mechanism;
* model `B` -> reconcile contradictory model evidence;
* only model `T` licenses direct interpretation of the world coordinate;
* world `N` or `B` under a trusted model -> gather more world evidence;
* trusted world `T/F` -> act positive/negative.
-/
def gate104ChooseAction (state : Gate103NestedStatus) : Gate104Action :=
  if state.model = FDEValue.N then
    .calibrateModel
  else if state.model = FDEValue.B then
    .reconcileModel
  else if state.model = FDEValue.F then
    .calibrateModel
  else if state.world = FDEValue.N then
    .senseWorld
  else if state.world = FDEValue.B then
    .senseWorld
  else if state.world = FDEValue.T then
    .actPositive
  else
    .actNegative

/-- Trusted truth licenses direct positive action. -/
theorem gate104_trusted_truth_acts_positive :
    gate104ChooseAction gate103TrustedTruth = .actPositive := by
  native_decide

/-- Trusted falsity licenses direct negative action. -/
theorem gate104_trusted_false_acts_negative :
    gate104ChooseAction gate103ResolvedFalseTrustedModel = .actNegative := by
  native_decide

/-- A model gap preempts a world verdict, even when the world coordinate is `T`. -/
theorem gate104_model_gap_calibrates_first :
    gate104ChooseAction gate103TruthWithModelGap = .calibrateModel := by
  native_decide

/-- Contradictory model evidence is treated differently from missing model evidence. -/
theorem gate104_model_conflict_reconciles_first :
    gate104ChooseAction gate103TruthWithModelConflict = .reconcileModel := by
  native_decide

/-- With a trusted model, first-order ignorance calls for more world evidence. -/
theorem gate104_world_gap_senses_world :
    gate104ChooseAction gate103WorldGapTrustedModel = .senseWorld := by
  native_decide

/-- With a trusted model, first-order contradiction also calls for discriminating world evidence. -/
theorem gate104_world_conflict_senses_world :
    gate104ChooseAction gate103WorldConflictTrustedModel = .senseWorld := by
  native_decide

/-- Second-order doubt has priority over an apparently decisive first-order truth. -/
theorem gate104_self_trust_preempts_world_action :
    gate103TruthWithModelGap.world = FDEValue.T ∧
    gate104ChooseAction gate103TruthWithModelGap = .calibrateModel ∧
    gate103TruthWithModelConflict.world = FDEValue.T ∧
    gate104ChooseAction gate103TruthWithModelConflict = .reconcileModel := by
  native_decide

/-- Direct world action occurs in the concrete witnesses only when the model
coordinate is strictly trusted. -/
theorem gate104_direct_action_requires_trusted_model_witness :
    gate103TrustedTruth.model = FDEValue.T ∧
    gate104ChooseAction gate103TrustedTruth = .actPositive ∧
    gate103ResolvedFalseTrustedModel.model = FDEValue.T ∧
    gate104ChooseAction gate103ResolvedFalseTrustedModel = .actNegative := by
  native_decide

/-- Main Gate-104 theorem: rational self-trust is a control discipline over two
independent four-valued layers. The controller repairs or interrogates its own
epistemic machinery before treating an uncertain or contradictory model layer as
a license for action on the world. -/
theorem gate104_rational_epistemic_self_trust :
    gate104ChooseAction gate103TrustedTruth = .actPositive ∧
    gate104ChooseAction gate103ResolvedFalseTrustedModel = .actNegative ∧
    gate104ChooseAction gate103TruthWithModelGap = .calibrateModel ∧
    gate104ChooseAction gate103TruthWithModelConflict = .reconcileModel ∧
    gate104ChooseAction gate103WorldGapTrustedModel = .senseWorld ∧
    gate104ChooseAction gate103WorldConflictTrustedModel = .senseWorld := by
  native_decide

/-!
## Gate-104 interpretation boundary

The verified theorem concerns this explicit deterministic priority policy and the
finite Gate-103 witnesses. It does not establish that this priority ordering is a
universal norm of rational agency. The philosophical result is therefore a model:
4PEL can represent an agent whose confidence in propositions and confidence in
its own evidence-generating mechanism are distinct, action-relevant quantities.
-/

end PEL4
