import PEL4.Paradoxes.ChurchFitch

namespace PEL4

/-!
# Source-side no-gap independence for Church--Fitch

`ChurchFitch.lean` shows that the positive Church--Fitch collapse requires a
source-side bridge from meta-level absence of positive knowledge to positive
support for internal epistemic negation:

  K+(phi) = false  ->  K-(phi) = true.

That bridge is exactly `ModalKnowledgeNoGapAt`.

This module gives a finite witness in which:

* `p` is strictly `T` at the source;
* `K p` is the gap value `N` at the source;
* therefore positive knowledge is absent;
* internal `not K p` has no positive support;
* the Moorean conjunction `p and not K p` is `N`, not positively true;
* the accessible candidate knowledge witness itself satisfies the previously
  verified local Fitch recovery package for `p`.

Thus the source-side no-gap transport is genuinely independent from the
witness-side recovery mechanism in this local sense.  Without it, the standard
Moorean construction can fail before knowability is even invoked.
-/

inductive FitchNoGapWorld where
  | actual | witness
deriving DecidableEq, Repr

/-- The actual point sees a homogeneous gappy witness; the witness is reflexive. -/
def fitchNoGapR : FitchAgent → FitchNoGapWorld → FiniteSet FitchNoGapWorld
  | _, FitchNoGapWorld.actual => [FitchNoGapWorld.witness]
  | _, FitchNoGapWorld.witness => [FitchNoGapWorld.witness]

/-- `p` is true at the source but gappy at the epistemic witness. -/
def fitchNoGapVal : FitchNoGapWorld → FitchAtom → FDEValue
  | FitchNoGapWorld.actual, _ => FDEValue.T
  | FitchNoGapWorld.witness, _ => FDEValue.N

/-- Exact normalized measure required by the ambient 4-PEL model structure. -/
def fitchNoGapMu : FiniteSet FitchNoGapWorld → Rat
  | S => if S.contains FitchNoGapWorld.witness then 1 else 0

/-- Two-world source-gap model. -/
def FitchNoGapModel : Model FitchNoGapWorld FitchAgent FitchAtom :=
  { worlds := [FitchNoGapWorld.actual, FitchNoGapWorld.witness]
  , R := fitchNoGapR
  , mu := fun _ _ => fitchNoGapMu
  , val := fitchNoGapVal
  , c := fun _ => 2 / 3
  , mu_total := by
      intro i w
      cases i
      cases w <;> native_decide
  , mu_empty := by
      intro i w
      cases i
      cases w <;> native_decide
  , c_gt_half := by
      intro i
      cases i
      native_decide
  , c_le_one := by
      intro i
      cases i
      native_decide
  }

/-- The source proposition is strictly true. -/
theorem fitch_no_gap_actual_p_is_true :
    evalModal FitchNoGapModel FitchNoGapWorld.actual fitchP = FDEValue.T := by
  native_decide

/-- Because the only epistemic alternative gives `p = N`, evidence-stable
knowledge also returns `N` at the source. -/
theorem fitch_no_gap_actual_kp_is_gap :
    evalModal FitchNoGapModel FitchNoGapWorld.actual
      (ModalFormula.know FitchAgent.a fitchP) = FDEValue.N := by
  native_decide

/-- The reflexive witness is homogeneous `N`, so `K p = N` there as well. -/
theorem fitch_no_gap_witness_kp_is_gap :
    evalModal FitchNoGapModel FitchNoGapWorld.witness
      (ModalFormula.know FitchAgent.a fitchP) = FDEValue.N := by
  native_decide

/-- The standard internal Moorean formula fails to become positively true:
`T and not N = T and N = N`. -/
theorem fitch_no_gap_actual_moore_is_gap :
    evalModal FitchNoGapModel FitchNoGapWorld.actual
      (modalMooreFormula FitchAgent.a fitchP) = FDEValue.N := by
  native_decide

/-- The source-side no-gap bridge fails exactly because `K p = N`: positive
knowledge is absent, yet negative support for the knowledge claim is absent too. -/
theorem fitch_source_no_gap_condition_fails :
    ¬ ModalKnowledgeNoGapAt
        FitchNoGapModel FitchAgent.a FitchNoGapWorld.actual fitchP := by
  intro hNoGap
  have hUnknown :
      modalLacksPositiveKnowledgeAt
        FitchNoGapModel FitchAgent.a FitchNoGapWorld.actual fitchP := by
    unfold modalLacksPositiveKnowledgeAt
    rw [fitch_no_gap_actual_kp_is_gap]
    rfl
  have hNeg := hNoGap hUnknown
  unfold modalNegativeKnowledgeAt at hNeg
  rw [fitch_no_gap_actual_kp_is_gap] at hNeg
  change false = true at hNeg
  cases hNeg

/-- The accessible witness still satisfies the complete witness-side local
recovery package for `p`: it is reflexive, `p` is stable there, and `K p` is
non-glutty. -/
theorem fitch_no_gap_witness_satisfies_local_recovery :
    ModalFitchLocalPackageAt
      FitchNoGapModel FitchAgent.a FitchNoGapWorld.witness fitchP := by
  unfold ModalFitchLocalPackageAt
  constructor
  · native_decide
  constructor
  · native_decide
  · intro hKpos
    rw [fitch_no_gap_witness_kp_is_gap] at hKpos
    change false = true at hKpos
    cases hKpos

/-- Local independence package for the source-side bridge.

The source has positive truth and lacks positive knowledge, while the internal
Moorean conjunction lacks positive truth.  At the same time the accessible
candidate witness already satisfies the witness-side recovery package. -/
theorem fitch_source_no_gap_transport_is_locally_independent :
    modalPositiveAt FitchNoGapModel FitchNoGapWorld.actual fitchP ∧
    modalLacksPositiveKnowledgeAt
      FitchNoGapModel FitchAgent.a FitchNoGapWorld.actual fitchP ∧
    ¬ modalPositiveAt FitchNoGapModel FitchNoGapWorld.actual
      (modalMooreFormula FitchAgent.a fitchP) ∧
    ¬ ModalKnowledgeNoGapAt
      FitchNoGapModel FitchAgent.a FitchNoGapWorld.actual fitchP ∧
    ModalFitchLocalPackageAt
      FitchNoGapModel FitchAgent.a FitchNoGapWorld.witness fitchP := by
  constructor
  · unfold modalPositiveAt
    rw [fitch_no_gap_actual_p_is_true]
    rfl
  constructor
  · unfold modalLacksPositiveKnowledgeAt
    rw [fitch_no_gap_actual_kp_is_gap]
    rfl
  constructor
  · intro hMoore
    unfold modalPositiveAt at hMoore
    rw [fitch_no_gap_actual_moore_is_gap] at hMoore
    change false = true at hMoore
    cases hMoore
  constructor
  · exact fitch_source_no_gap_condition_fails
  · exact fitch_no_gap_witness_satisfies_local_recovery

/-!
## Interpretation

The positive Church--Fitch argument therefore has a genuine source-side failure
mode in addition to the three witness-side escape routes already formalized.

If `K phi = N`, then meta-level unknownness is present but internal `not K phi`
is not positively supported.  The Moorean sentence needed by the classical
construction is not positively true, so a positive knowability principle has
nothing to apply to at that step.

This is a local irredundancy result for the no-gap transport.  It is deliberately
weaker than a global independence theorem for the fully quantified Church--Fitch
schema, whose knowability and recovery assumptions range over all modal formulas.
-/

end PEL4
