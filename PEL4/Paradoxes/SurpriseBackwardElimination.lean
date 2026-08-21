import PEL4.Paradoxes.SurpriseExamination
import PEL4.StructuralTransport

namespace PEL4.Paradoxes

/-!
# Surprise Examination: backward elimination as context transport

The dynamic Surprise model already proves the chronological trajectory

  M0 --not Monday--> M1 --not Wednesday--> M2

and, for the Friday proposition, the belief path

  F -> N -> T.

This file isolates the backward-elimination reasoning itself. The crucial
observation is that its three prediction steps are made in three different
counterfactual epistemic contexts:

* Friday is predictable after Monday and Wednesday have actually been excluded;
* Wednesday is predictable after Friday is hypothetically ruled out and Monday
  has been excluded;
* Monday is predictable after Friday and Wednesday are hypothetically ruled out.

Each prediction is correct inside its own context. The transport error appears
when those context-indexed predictions are treated as if they were predictions
already available in the original model M0.
-/

/-- Counterfactual branch used after the backward reasoner rules out Friday. -/
def SurpriseNoFri : Model SurpriseWorld SurpriseAgent SurpriseAtom :=
  conditionalize SurpriseModel0 notFri

/-- In the no-Friday branch, Monday has also passed without an exam. -/
def SurpriseNoFriNoMon : Model SurpriseWorld SurpriseAgent SurpriseAtom :=
  conditionalize SurpriseNoFri notMon

/-- Counterfactual branch after Friday and Wednesday have both been ruled out. -/
def SurpriseNoFriNoWed : Model SurpriseWorld SurpriseAgent SurpriseAtom :=
  conditionalize SurpriseNoFri notWed

/-- Friday is predictable in the actual late-week context. -/
def backwardPredictsFriday : Bool :=
  positivelyPredicts SurpriseModel2 examFri

/-- Wednesday is predictable only in the branch where Friday is already ruled
out and Monday has passed without an exam. -/
def backwardPredictsWednesday : Bool :=
  positivelyPredicts SurpriseNoFriNoMon examWed

/-- Monday is predictable in the branch where both later days are already
ruled out. -/
def backwardPredictsMonday : Bool :=
  positivelyPredicts SurpriseNoFriNoWed examMon

/-- The three backward-elimination justifications are locally correct in their
respective counterfactual contexts. -/
theorem backward_elimination_local_predictions :
    backwardPredictsFriday = true ∧
    backwardPredictsWednesday = true ∧
    backwardPredictsMonday = true := by
  native_decide

/-- Initial prediction status for a day in the original model. -/
def initiallyPredicts (day : SurpriseAtom) : Bool :=
  match day with
  | SurpriseAtom.mon => positivelyPredicts SurpriseModel0 examMon
  | SurpriseAtom.wed => positivelyPredicts SurpriseModel0 examWed
  | SurpriseAtom.fri => positivelyPredicts SurpriseModel0 examFri

/-- Branch-relative backward prediction status. This deliberately packages
three different epistemic contexts into one meta-level classifier. -/
def backwardContextPredicts (day : SurpriseAtom) : Bool :=
  match day with
  | SurpriseAtom.mon => backwardPredictsMonday
  | SurpriseAtom.wed => backwardPredictsWednesday
  | SurpriseAtom.fri => backwardPredictsFriday

/-- Every day is predictable in the special context used to eliminate that day,
while no day is positively predictable in the initial epistemic context. -/
theorem backward_context_prediction_does_not_transport_to_initial
    (day : SurpriseAtom) :
    backwardContextPredicts day = true ∧ initiallyPredicts day = false := by
  cases day <;> native_decide

/-- The backward reasoner therefore classifies all three days as eliminable,
even though the original model positively predicts none of them. -/
theorem all_backward_eliminable_but_none_initially_predicted :
    backwardContextPredicts SurpriseAtom.mon = true ∧
    backwardContextPredicts SurpriseAtom.wed = true ∧
    backwardContextPredicts SurpriseAtom.fri = true ∧
    initiallyPredicts SurpriseAtom.mon = false ∧
    initiallyPredicts SurpriseAtom.wed = false ∧
    initiallyPredicts SurpriseAtom.fri = false := by
  native_decide

/-- The two intermediate counterfactual predictions are genuinely created by
conditioning: Wednesday is not initially predicted, and Monday is not initially
predicted, although both become predictable in their elimination contexts. -/
theorem backward_prediction_is_context_created :
    initiallyPredicts SurpriseAtom.wed = false ∧
    backwardPredictsWednesday = true ∧
    initiallyPredicts SurpriseAtom.mon = false ∧
    backwardPredictsMonday = true := by
  native_decide

/-- Structural-transport formulation of the backward-elimination mistake.

The identity map on exam days does not transport the predicate "predictable in
the day-specific elimination context" to the predicate "predictable in the
initial context". -/
def backwardPredictionTransport : Prop :=
  TransportsPredicate
    (fun day : SurpriseAtom => day)
    (fun day => backwardContextPredicts day = true)
    (fun day => initiallyPredicts day = true)

/-- The Surprise backward argument gives the first direct paradox-level witness
that the generic structural-transport predicate can fail. -/
theorem backward_prediction_transport_fails :
    ¬ backwardPredictionTransport := by
  unfold backwardPredictionTransport
  apply transport_fails_of_witness
    (T := fun day : SurpriseAtom => day)
    (P := fun day => backwardContextPredicts day = true)
    (Q := fun day => initiallyPredicts day = true)
    (x := SurpriseAtom.fri)
  · native_decide
  · native_decide

/-!
## Interpretation

The backward argument need not contain a locally invalid inference. Its local
prediction claims can all be correct. What fails is structural transport across
contexts.

The three claims

  predict Friday in C_F,
  predict Wednesday in C_W,
  predict Monday in C_M

are evaluated in distinct updated/counterfactual models. They do not entail

  predict Friday in M0,
  predict Wednesday in M0,
  predict Monday in M0.

Thus the paradox can be diagnosed as a context-collapse error: branch-relative
predictability is projected into a context-free eliminability judgement and
then transported back to the initial epistemic state.

The theorem `backward_prediction_transport_fails` now states this diagnosis in
the shared generic language of `StructuralTransport.lean`, rather than leaving
"transport failure" as interpretation alone.

This is stronger than saying merely that belief is non-monotone under update.
The earlier Surprise module establishes dynamic threshold crossing; this module
isolates the additional backward-induction mistake of conflating predictions
made in different epistemic contexts.
-/

end PEL4.Paradoxes
