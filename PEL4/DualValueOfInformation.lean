import PEL4.JointEpistemicControl

namespace PEL4

/-!
# Gate 91: dual value of information

Gate 90 made second-order model trust control-relevant. Gate 91 separates the
informational value of an experiment into two exact rational components:
reduction of uncertainty about the world and reduction of uncertainty about the
observation model.

For a binary marginal we use the exact impurity `p(1-p)`. This is not Shannon
entropy; it is a Lean-friendly finite witness of two distinct informational axes.
-/

def gate91BinaryUncertainty (p : Rat) : Rat := p * (1 - p)

def gate91PriorUncertainty : Rat := gate91BinaryUncertainty ((1 : Rat) / 2)

inductive Gate91Experiment where
  | worldProbe
  | calibration
  deriving DecidableEq, Repr

/-- Expected residual world uncertainty after the experiment. -/
def gate91WorldResidual : Gate91Experiment → Rat
  | .worldProbe => 0
  | .calibration => (3 : Rat) / 16

/-- Expected residual sensor-model uncertainty after the experiment. -/
def gate91ModelResidual : Gate91Experiment → Rat
  | .worldProbe => (1 : Rat) / 4
  | .calibration => 0

def gate91WorldInformationValue (e : Gate91Experiment) : Rat :=
  gate91PriorUncertainty - gate91WorldResidual e

def gate91ModelInformationValue (e : Gate91Experiment) : Rat :=
  gate91PriorUncertainty - gate91ModelResidual e

/-- Equal-weight epistemic value of both dimensions. -/
def gate91TotalInformationValue (e : Gate91Experiment) : Rat :=
  gate91WorldInformationValue e + gate91ModelInformationValue e

theorem gate91_prior_uncertainty :
    gate91PriorUncertainty = (1 : Rat) / 4 := by
  native_decide

theorem gate91_world_probe_profile :
    gate91WorldInformationValue .worldProbe = (1 : Rat) / 4 ∧
    gate91ModelInformationValue .worldProbe = 0 ∧
    gate91TotalInformationValue .worldProbe = (1 : Rat) / 4 := by
  native_decide

theorem gate91_calibration_profile :
    gate91WorldInformationValue .calibration = (1 : Rat) / 16 ∧
    gate91ModelInformationValue .calibration = (1 : Rat) / 4 ∧
    gate91TotalInformationValue .calibration = (5 : Rat) / 16 := by
  native_decide

/-- Calibration can be worse on first-order world learning yet better overall
because it resolves second-order uncertainty about the evidence mechanism. -/
theorem gate91_less_world_information_can_have_more_total_value :
    gate91WorldInformationValue .calibration < gate91WorldInformationValue .worldProbe ∧
    gate91ModelInformationValue .calibration > gate91ModelInformationValue .worldProbe ∧
    gate91TotalInformationValue .calibration > gate91TotalInformationValue .worldProbe := by
  native_decide

/-!
## Gate-91 boundary

The residual uncertainties are a concrete experiment profile. Gate 91 does not
yet derive them from a generic observation kernel and does not identify this
quadratic impurity with Shannon mutual information. The verified claim is the
existence of two separately valuable epistemic dimensions and an exact witness
where model information reverses the ranking induced by world information alone.
-/

end PEL4
