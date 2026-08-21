import PEL4.Paradoxes.ChurchFitchNoGapIndependence

namespace PEL4

/-!
# Church--Fitch phase landscape

The positive Church--Fitch theorem is now verified for positive/designated truth
and primitive raw accessibility possibility.  This module begins the comparison
of two independent axes that are classically easy to conflate:

1. source truth: positive/designated truth versus strict `T`;
2. possibility: primitive raw `Diamond` versus the internal knowledge dual
   `not K(not ...)`.

The first axis changes how much is required to build the Moorean sentence.  If
`phi` is strictly `T`, source no-gap plus lack of positive knowledge makes
`K phi = F`, so `phi and not K phi` is itself strictly `T`.

The second axis is asymmetric.  Raw positive possibility exposes an actual
accessible positive witness.  The internal dual can instead become positively
true merely because the relevant accessible FDE profile is unstable.
-/

/-!
## 1. Strict-T truth phase
-/

/-- Knowability restricted to strictly `T` truths, while the knowability
conclusion remains positive raw possibility of knowledge. -/
def ModalStrictTruthPositiveKnowabilityPrinciple
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ (w : W) (phi : ModalFormula Atom Ag),
    w ∈ m.worlds →
    modalStrictTrueAt m w phi →
    modalPositiveKnowableAt m i w phi

/-- Positive knowledge of every strictly `T` truth. -/
def ModalStrictTruthPositiveOmniscience
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ (w : W) (phi : ModalFormula Atom Ag),
    w ∈ m.worlds →
    modalStrictTrueAt m w phi →
    modalPositiveKnownAt m i w phi

/-- Strong strict omniscience: every strictly `T` truth is itself strictly
`T`-known. -/
def ModalStrictKnowledgeOmniscience
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ (w : W) (phi : ModalFormula Atom Ag),
    w ∈ m.worlds →
    modalStrictTrueAt m w phi →
    evalModal m w (ModalFormula.know i phi) = FDEValue.T

/-- The positive/designated knowability principle is stronger than its
strict-truth restriction. -/
theorem positive_knowability_implies_strict_truth_positive_knowability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (h : ModalPositiveKnowabilityPrinciple m i) :
    ModalStrictTruthPositiveKnowabilityPrinciple m i := by
  intro w phi hw hT
  exact h w phi hw (modal_strict_true_implies_positive m w phi hT)

/-- Under source no-gap, a strictly true but positively unknown formula yields a
strictly true Moorean conjunction. -/
theorem modal_moore_strict_true_of_strict_truth_unknown_no_gap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrue : modalStrictTrueAt m w phi)
    (hUnknown : modalLacksPositiveKnowledgeAt m i w phi)
    (hNoGap : ModalKnowledgeNoGapAt m i w phi) :
    modalStrictTrueAt m w (modalMooreFormula i phi) := by
  have hNeg : modalNegativeKnowledgeAt m i w phi :=
    hNoGap hUnknown
  have hK :
      evalModal m w (ModalFormula.know i phi) = FDEValue.F := by
    unfold modalLacksPositiveKnowledgeAt at hUnknown
    unfold modalNegativeKnowledgeAt at hNeg
    cases hVal : evalModal m w (ModalFormula.know i phi) with
    | mk pos neg =>
        cases pos <;> cases neg <;> simp_all [FDEValue.F]
  unfold modalStrictTrueAt at hTrue ⊢
  unfold modalMooreFormula
  change FDEValue.and (evalModal m w phi)
      (FDEValue.not (evalModal m w (ModalFormula.know i phi))) = FDEValue.T
  rw [hTrue, hK]
  rfl

/-- Strict-truth Church--Fitch phase.

A knowability principle restricted to strict truths already suffices to force
positive knowledge of every strict truth, because the Moorean sentence generated
from a strict truth is itself strict under the source no-gap bridge. -/
theorem church_fitch_strict_truth_positive_omniscience_of_strict_knowability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hKnowability : ModalStrictTruthPositiveKnowabilityPrinciple m i)
    (hNoGap : ∀ (w : W) (phi : ModalFormula Atom Ag),
      w ∈ m.worlds → ModalKnowledgeNoGapAt m i w phi)
    (hRecovery : ModalUniformFitchRecovery m i) :
    ModalStrictTruthPositiveOmniscience m i := by
  intro w phi hw hTrue
  unfold modalPositiveKnownAt
  cases hK : (evalModal m w (ModalFormula.know i phi)).pos with
  | true =>
      rfl
  | false =>
      have hUnknown : modalLacksPositiveKnowledgeAt m i w phi := hK
      have hMooreT : modalStrictTrueAt m w (modalMooreFormula i phi) :=
        modal_moore_strict_true_of_strict_truth_unknown_no_gap
          m i w phi hTrue hUnknown (hNoGap w phi hw)
      have hKnowableMoore :
          modalPositiveKnowableAt m i w (modalMooreFormula i phi) :=
        hKnowability w (modalMooreFormula i phi) hw hMooreT
      have hPoss :
          (evalModal m w (modalRawKnowabilityOfMoore i phi)).pos = true := by
        simpa [modalPositiveKnowableAt, modalRawKnowabilityOfMoore,
          modalKnowledgeOfMoore] using hKnowableMoore
      rcases raw_fitch_knowability_requires_local_escape
          m i w phi hPoss with
        ⟨w', hw', _, hEscape⟩
      have hPackage : ModalFitchLocalPackageAt m i w' phi :=
        hRecovery w phi hw w' hw'
      exact False.elim (hEscape hPackage)

/-- If source knowledge is additionally non-glutty, the strict-truth phase
strengthens from positive knowledge to strict `T` knowledge. -/
theorem church_fitch_strict_knowledge_omniscience_of_strict_knowability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hKnowability : ModalStrictTruthPositiveKnowabilityPrinciple m i)
    (hNoGap : ∀ (w : W) (phi : ModalFormula Atom Ag),
      w ∈ m.worlds → ModalKnowledgeNoGapAt m i w phi)
    (hRecovery : ModalUniformFitchRecovery m i)
    (hSourceNoGlut : ∀ (w : W) (phi : ModalFormula Atom Ag),
      w ∈ m.worlds → ModalKnowledgeNoGlutAt m i w phi) :
    ModalStrictKnowledgeOmniscience m i := by
  intro w phi hw hTrue
  have hPos : modalPositiveKnownAt m i w phi :=
    church_fitch_strict_truth_positive_omniscience_of_strict_knowability
      m i hKnowability hNoGap hRecovery w phi hw hTrue
  have hNegFalse :
      (evalModal m w (ModalFormula.know i phi)).neg = false :=
    hSourceNoGlut w phi hw hPos
  unfold modalPositiveKnownAt at hPos
  cases hVal : evalModal m w (ModalFormula.know i phi) with
  | mk pos neg =>
      cases pos <;> cases neg <;> simp_all [FDEValue.T]

/-!
## 2. Raw possibility versus internal dual phase
-/

/-- Positive possibility according to the internal knowledge dual rather than
primitive raw accessibility possibility. -/
def modalDualPositivePossibleAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (psi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.knowledgeDual i psi)).pos = true

/-- Dualized positive knowability of `phi`: positive support for
`not K(not K phi)`. -/
def modalDualPositiveKnowableAt
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  modalDualPositivePossibleAt m i w (ModalFormula.know i phi)

/-- Raw positive possibility always implies positive internal-dual possibility.
The converse will fail below. -/
theorem modal_raw_positive_implies_dual_positive
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (psi : ModalFormula Atom Ag)
    (hRaw : (evalModal m w (ModalFormula.poss i psi)).pos = true) :
    modalDualPositivePossibleAt m i w psi := by
  have hAny :
      (m.R i w).any (fun w' => (evalModal m w' psi).pos) = true := by
    simpa [evalModal, modalRawPossibilityValue] using hRaw
  unfold modalDualPositivePossibleAt ModalFormula.knowledgeDual
  simp [evalModal, modalKnowledgeValue, FDEValue.not, hAny]

/-- Consequently primitive raw positive knowability implies dualized positive
knowability. -/
theorem modal_raw_positive_knowability_implies_dual_positive_knowability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hRaw : modalPositiveKnowableAt m i w phi) :
    modalDualPositiveKnowableAt m i w phi := by
  unfold modalPositiveKnowableAt at hRaw
  unfold modalDualPositiveKnowableAt
  exact modal_raw_positive_implies_dual_positive
    m i w (ModalFormula.know i phi) hRaw

/-!
### A direct Fitch-shaped dualization witness

The root sees two worlds.  At one, `K p = N`; at the other, `K p = F`.
Therefore raw possibility of `K p` is `N`: no accessible world positively knows
`p`.  But the profile is unstable, so the internal dual `not K(not K p)` becomes
strict `T`.
-/

inductive FitchDualWorld where
  | root | gap | falseWorld
deriving DecidableEq, Repr

def fitchDualR : FitchAgent → FitchDualWorld → FiniteSet FitchDualWorld
  | _, FitchDualWorld.root => [FitchDualWorld.gap, FitchDualWorld.falseWorld]
  | _, FitchDualWorld.gap => [FitchDualWorld.gap]
  | _, FitchDualWorld.falseWorld => [FitchDualWorld.falseWorld]

def fitchDualVal : FitchDualWorld → FitchAtom → FDEValue
  | FitchDualWorld.root, _ => FDEValue.T
  | FitchDualWorld.gap, _ => FDEValue.N
  | FitchDualWorld.falseWorld, _ => FDEValue.F

def fitchDualMu : FitchDualWorld → FiniteSet FitchDualWorld → Rat
  | FitchDualWorld.root, S =>
      let pg := if S.contains FitchDualWorld.gap then (1 : Rat) / 2 else 0
      let pf := if S.contains FitchDualWorld.falseWorld then (1 : Rat) / 2 else 0
      pg + pf
  | FitchDualWorld.gap, S =>
      if S.contains FitchDualWorld.gap then 1 else 0
  | FitchDualWorld.falseWorld, S =>
      if S.contains FitchDualWorld.falseWorld then 1 else 0

def FitchDualModel : Model FitchDualWorld FitchAgent FitchAtom :=
  { worlds := [FitchDualWorld.root, FitchDualWorld.gap,
      FitchDualWorld.falseWorld]
  , R := fitchDualR
  , mu := fun _ w => fitchDualMu w
  , val := fitchDualVal
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

/-- The source proposition is a strict truth. -/
theorem fitch_dual_root_p_is_strict_true :
    evalModal FitchDualModel FitchDualWorld.root fitchP = FDEValue.T := by
  native_decide

/-- At the gappy child, `K p = N`. -/
theorem fitch_dual_gap_kp_is_gap :
    evalModal FitchDualModel FitchDualWorld.gap
      (ModalFormula.know FitchAgent.a fitchP) = FDEValue.N := by
  native_decide

/-- At the false child, `K p = F`. -/
theorem fitch_dual_false_kp_is_false :
    evalModal FitchDualModel FitchDualWorld.falseWorld
      (ModalFormula.know FitchAgent.a fitchP) = FDEValue.F := by
  native_decide

/-- Primitive raw knowability finds no positive knowledge witness and is `N`. -/
theorem fitch_dual_raw_knowability_is_gap :
    evalModal FitchDualModel FitchDualWorld.root
      (ModalFormula.poss FitchAgent.a
        (ModalFormula.know FitchAgent.a fitchP)) = FDEValue.N := by
  native_decide

/-- Internal-dual knowability is nevertheless strict `T`, generated by
instability of the `N/F` knowledge profile. -/
theorem fitch_dual_internal_knowability_is_true :
    evalModal FitchDualModel FitchDualWorld.root
      (ModalFormula.knowledgeDual FitchAgent.a
        (ModalFormula.know FitchAgent.a fitchP)) = FDEValue.T := by
  native_decide

/-- A strict truth can therefore be dual-positively "knowable" while primitive
raw knowability is absent.  The dualized reading does not guarantee an
accessible positive knowledge witness. -/
theorem fitch_dual_knowability_without_raw_knowability :
    modalStrictTrueAt FitchDualModel FitchDualWorld.root fitchP ∧
    modalDualPositiveKnowableAt
      FitchDualModel FitchAgent.a FitchDualWorld.root fitchP ∧
    ¬ modalPositiveKnowableAt
      FitchDualModel FitchAgent.a FitchDualWorld.root fitchP := by
  constructor
  · unfold modalStrictTrueAt
    exact fitch_dual_root_p_is_strict_true
  constructor
  · unfold modalDualPositiveKnowableAt modalDualPositivePossibleAt
    rw [fitch_dual_internal_knowability_is_true]
    rfl
  · intro hRaw
    unfold modalPositiveKnowableAt at hRaw
    rw [fitch_dual_raw_knowability_is_gap] at hRaw
    change false = true at hRaw
    cases hRaw

/-!
## Interpretation

The first phase map is asymmetric in both axes.

Truth axis:

* positive truth needs the source no-gap bridge to make the Moorean sentence
  positively true;
* strict `T` truth plus the same bridge makes the Moorean sentence strictly `T`;
* therefore a knowability schema restricted to strict truths can already force
  positive omniscience over strict truths;
* adding source no-glut upgrades the conclusion to strict `T` knowledge.

Possibility axis:

* raw positive possibility implies positive internal-dual possibility;
* internal-dual possibility does not imply raw positive possibility;
* in the finite witness, a strict truth has dualized "knowability" even though
  no accessible world positively knows it.

Thus replacing primitive raw `Diamond` by `not K not` can strengthen the
antecedent in exactly the wrong way for Church--Fitch analysis: epistemic
instability may masquerade as possibility.
-/

end PEL4