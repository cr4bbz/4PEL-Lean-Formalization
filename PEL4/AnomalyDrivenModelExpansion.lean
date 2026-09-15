import PEL4.PosteriorSurprise

namespace PEL4

/-!
# Gate 100: anomaly-driven model expansion

Gate 99 detects observations that are too surprising for ordinary closed-class
updating. Gate 100 turns that meta-level doubt into a structural control action:
keep the current hypothesis class for routine evidence, but open the model space
when predictive evidence falls below the surprise threshold.
-/

inductive Gate100ModelSpaceAction where
  | keepClosed
  | expandUnknown
  deriving DecidableEq, Repr

/-- Structural policy driven directly by predictive adequacy. -/
def gate100ChooseModelSpaceAction (obs : Gate99Observation) : Gate100ModelSpaceAction :=
  if gate99PredictiveEvidence obs < gate99SurpriseThreshold then
    .expandUnknown
  else
    .keepClosed

/-- Routine evidence leaves the known model class untouched. -/
theorem gate100_routine_keeps_closed_class :
    gate100ChooseModelSpaceAction .routine = .keepClosed := by
  native_decide

/-- The anomaly from Gate 99 triggers explicit model-space expansion. -/
theorem gate100_anomaly_expands_model_space :
    gate100ChooseModelSpaceAction .anomaly = .expandUnknown := by
  native_decide

/-- The structural action agrees exactly with the Gate-99 meta-mode on both
concrete observations. -/
theorem gate100_action_tracks_meta_mode :
    (gate99MetaUpdate .routine = .normalUpdate ∧
      gate100ChooseModelSpaceAction .routine = .keepClosed) ∧
    (gate99MetaUpdate .anomaly = .modelDoubt ∧
      gate100ChooseModelSpaceAction .anomaly = .expandUnknown) := by
  native_decide

/-- The anomaly is not merely relabeled: its predictive probability lies below
the threshold that causes a change to the hypothesis space itself. -/
theorem gate100_expansion_is_surprise_triggered :
    gate99PredictiveEvidence .anomaly = (3 : Rat) / 200 ∧
    gate99PredictiveEvidence .anomaly < gate99SurpriseThreshold ∧
    gate100ChooseModelSpaceAction .anomaly = .expandUnknown := by
  native_decide

/-- Main Gate-100 theorem: sufficiently surprising evidence changes the structure
of inference rather than only redistributing mass among already-known models. -/
theorem gate100_anomaly_driven_model_expansion :
    gate100ChooseModelSpaceAction .routine = .keepClosed ∧
    gate100ChooseModelSpaceAction .anomaly = .expandUnknown ∧
    gate99MetaUpdate .anomaly = .modelDoubt := by
  native_decide

/-!
## Boundary

Gate 100 decides when to expand, not how to invent the new model. Gate 101 gives
the resulting outside-class possibility explicit probability mass and maps it to
4PEL meta-status.
-/

end PEL4
