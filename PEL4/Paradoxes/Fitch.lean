import PEL4.ModalLanguage

namespace PEL4

/-!
# Fitch knowability gate

This module is the first object-language Fitch experiment for the conservative
modal extension of 4-PEL.

The classical Fitch argument considers a Moorean truth

  p and not K(p)

and, from its knowability, moves to a possible state satisfying

  K(p and not K(p)).

A crucial classical step then extracts `K(p)` from knowledge of the conjunction.
The preceding semantic gates showed abstractly that evidence-stable knowledge
need not support this decomposition.  Here the right conjunct is no longer an
independent atom: it is literally the object-language formula `not K(p)`.

The witness world used below is reflexive.  Thus the failure cannot be dismissed
as merely an artefact of lacking local factivity at the critical Fitch point.
-/

inductive FitchAtom where
  | p
deriving DecidableEq, Repr

inductive FitchAgent where
  | a
deriving DecidableEq, Repr

inductive FitchWorld where
  | actual
  | witness
  | left
  | right
  | source
  | leftSrc
deriving DecidableEq, Repr

/-- Accessibility is arranged so that the critical `witness` point is reflexive,
while the full FDE value of `p` varies across its accessible range. -/
def fitchR : FitchAgent → FitchWorld → FiniteSet FitchWorld
  | _, FitchWorld.actual => [FitchWorld.witness, FitchWorld.source]
  | _, FitchWorld.witness => [FitchWorld.witness, FitchWorld.left, FitchWorld.right]
  | _, FitchWorld.left => [FitchWorld.leftSrc]
  | _, FitchWorld.right => [FitchWorld.left, FitchWorld.right]
  | _, FitchWorld.source => [FitchWorld.source]
  | _, FitchWorld.leftSrc => [FitchWorld.leftSrc]

/-- Valuation chosen to make the Moorean conjunction stable at the critical
accessible cluster while `p` itself remains unstable there. -/
def fitchVal : FitchWorld → FitchAtom → FDEValue
  | FitchWorld.actual, _ => FDEValue.T
  | FitchWorld.witness, _ => FDEValue.B
  | FitchWorld.left, _ => FDEValue.T
  | FitchWorld.right, _ => FDEValue.B
  | FitchWorld.source, _ => FDEValue.F
  | FitchWorld.leftSrc, _ => FDEValue.B

/-- Context-indexed exact rational measure.  The modal `K` and raw possibility
operators do not use these probabilities, but an ordinary 4-PEL `Model` still
requires normalized measures. -/
def fitchMu : FitchWorld → FiniteSet FitchWorld → Rat
  | FitchWorld.actual, S =>
      let pw := if S.contains FitchWorld.witness then (1 : Rat) / 2 else 0
      let ps := if S.contains FitchWorld.source then (1 : Rat) / 2 else 0
      pw + ps
  | FitchWorld.witness, S =>
      let pw := if S.contains FitchWorld.witness then (1 : Rat) / 3 else 0
      let pl := if S.contains FitchWorld.left then (1 : Rat) / 3 else 0
      let pr := if S.contains FitchWorld.right then (1 : Rat) / 3 else 0
      pw + pl + pr
  | FitchWorld.left, S =>
      if S.contains FitchWorld.leftSrc then 1 else 0
  | FitchWorld.right, S =>
      let pl := if S.contains FitchWorld.left then (1 : Rat) / 2 else 0
      let pr := if S.contains FitchWorld.right then (1 : Rat) / 2 else 0
      pl + pr
  | FitchWorld.source, S =>
      if S.contains FitchWorld.source then 1 else 0
  | FitchWorld.leftSrc, S =>
      if S.contains FitchWorld.leftSrc then 1 else 0

/-- Finite Fitch witness model. -/
def FitchModel : Model FitchWorld FitchAgent FitchAtom :=
  { worlds := [FitchWorld.actual, FitchWorld.witness, FitchWorld.left,
      FitchWorld.right, FitchWorld.source, FitchWorld.leftSrc]
  , R := fitchR
  , mu := fun _ w => fitchMu w
  , val := fitchVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro _ w
      cases w <;> native_decide
  , mu_empty := by
      intro _ w
      cases w <;> native_decide
  , c_gt_half := by
      intro _
      native_decide
  , c_le_one := by
      intro _
      native_decide
  }

/-- Atomic Fitch proposition. -/
def fitchP : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.prop FitchAtom.p

/-- `K p`. -/
def fitchKP : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.know FitchAgent.a fitchP

/-- Internal Moorean negation `not K p`. -/
def fitchNotKP : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.not fitchKP

/-- Moorean conjunction `p and not K p`. -/
def fitchMoore : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.and fitchP fitchNotKP

/-- Knowledge of the Moorean conjunction. -/
def fitchKMoore : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.know FitchAgent.a fitchMoore

/-- Raw knowability of the Moorean conjunction: `Diamond_raw K(p and not K p)`. -/
def fitchKnowableMoore : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.poss FitchAgent.a fitchKMoore

/-- The classical contradiction-shaped formula `K p and not K p`. -/
def fitchKnowledgeContradiction : ModalFormula FitchAtom FitchAgent :=
  ModalFormula.and fitchKP fitchNotKP

/-- The actual state realizes a strict Moorean truth. -/
theorem fitch_actual_moore_is_true :
    evalModal FitchModel FitchWorld.actual fitchMoore = FDEValue.T := by
  native_decide

/-- The Moorean truth is positively raw-knowable.  Its full possibility value is
`B`, so positive possibility is present without collapsing the negative side. -/
theorem fitch_actual_moore_is_raw_knowable :
    evalModal FitchModel FitchWorld.actual fitchKnowableMoore = FDEValue.B := by
  native_decide

/-- The critical possible state is reflexive for the Fitch agent. -/
theorem fitch_witness_is_reflexive :
    FitchWorld.witness ∈ FitchModel.R FitchAgent.a FitchWorld.witness := by
  native_decide

/-- At the critical possible state, the Moorean conjunction itself is glutty. -/
theorem fitch_witness_moore_is_glut :
    evalModal FitchModel FitchWorld.witness fitchMoore = FDEValue.B := by
  native_decide

/-- Evidence-stable knowledge of the Moorean conjunction is positively true but
also negatively supported: `K(p and not K p) = B`. -/
theorem fitch_witness_knows_moore_gluttily :
    evalModal FitchModel FitchWorld.witness fitchKMoore = FDEValue.B := by
  native_decide

/-- Nevertheless `K p` is strictly false at that same reflexive world because
`p` has the unstable accessible profile `B/T/B`. -/
theorem fitch_witness_kp_is_false :
    evalModal FitchModel FitchWorld.witness fitchKP = FDEValue.F := by
  native_decide

/-- Knowledge of the right Moorean conjunct also fails: the accessible values of
`not K p` vary between `T` and `B`. -/
theorem fitch_witness_k_not_kp_is_false :
    evalModal FitchModel FitchWorld.witness
      (ModalFormula.know FitchAgent.a fitchNotKP) = FDEValue.F := by
  native_decide

/-- Exact Fitch-shaped conjunction-extraction failure.

Positive evidence-stable knowledge of `p and not K p` does not transport to
positive evidence-stable knowledge of either component. -/
theorem fitch_knowledge_conjunction_extraction_fails :
    (evalModal FitchModel FitchWorld.witness fitchKMoore).pos = true ∧
    (evalModal FitchModel FitchWorld.witness fitchKP).pos = false ∧
    (evalModal FitchModel FitchWorld.witness
      (ModalFormula.know FitchAgent.a fitchNotKP)).pos = false := by
  native_decide

/-- The semantic reason is the same stability-reflection failure isolated by the
abstract conjunction gate: the Moorean compound is stable over the critical
accessible cluster while both components are unstable there. -/
theorem fitch_moore_masks_component_instability :
    modalAccessibleValueStable
        (FitchModel.R FitchAgent.a FitchWorld.witness)
        (fun w' => evalModal FitchModel w' fitchMoore) = true ∧
    modalAccessibleValueStable
        (FitchModel.R FitchAgent.a FitchWorld.witness)
        (fun w' => evalModal FitchModel w' fitchP) = false ∧
    modalAccessibleValueStable
        (FitchModel.R FitchAgent.a FitchWorld.witness)
        (fun w' => evalModal FitchModel w' fitchNotKP) = false := by
  native_decide

/-- The contradiction used in the classical Fitch reductio is not obtained at
the witness: `K p and not K p` is strictly false rather than glutty. -/
theorem fitch_classical_knowledge_contradiction_does_not_arise :
    evalModal FitchModel FitchWorld.witness fitchKnowledgeContradiction =
      FDEValue.F := by
  native_decide

/-!
## Interpretation

This model validates the first object-language fracture point in the Fitch
argument.

At the actual state:

  p and not K p = T
  Diamond_raw K(p and not K p) = B

so the Moorean truth is positively knowable.  At a reflexive possible witness:

  K(p and not K p) = B
  K p = F
  K(not K p) = F.

The knowledge-of-conjunction premise therefore has positive support, yet neither
knowledge conjunct can be extracted.  The reason is not failure of ordinary
truth-functional conjunction elimination and not absence of local reflexivity.
It is the already identified failure of component-level FDE stability
reflection.

This does not yet prove a general anti-Fitch theorem.  It supplies a concrete
object-language witness showing that the classical derivation cannot use
knowledge-conjunction elimination unrestrictedly in the present semantics.
The next gate should isolate which extra stability or strictness assumptions
restore the classical step and then formulate the minimal package needed for a
full Fitch collapse theorem.
-/

end PEL4
