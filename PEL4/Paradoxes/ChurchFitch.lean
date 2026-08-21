import PEL4.ModalValidity
import PEL4.Paradoxes.FitchKnowabilityBoundary

namespace PEL4

/-!
# Positive Church--Fitch theorem gate

The previous Fitch modules isolate the witness-side recovery package:

  reflexivity + Stable(phi) + NoGlut(K phi).

To recover the classical Church--Fitch move from a positively true but not
positively known `phi` to the Moorean formula

  phi and not K phi,

one additional source-side transport is required in a four-valued setting.
Meta-level absence of positive knowledge is not generally the same as positive
support for internal `not K phi`.  The missing bridge is a local no-gap
condition on the knowledge value:

  K+(phi) = false -> K-(phi) = true.

This module makes that bridge explicit and then proves a positive/designated
Church--Fitch omniscience theorem under a quantified knowability principle and
uniform witness-side recovery.
-/

/-- Local no-gap condition for a knowledge value.  Whenever positive knowledge
is absent, negative support for that knowledge claim is present.  This rules out
`N` in precisely the case used by the Moorean construction. -/
def ModalKnowledgeNoGapAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  modalLacksPositiveKnowledgeAt m i w phi →
    modalNegativeKnowledgeAt m i w phi

/-- Uniform witness-side Fitch recovery for every formula at every world listed
in the source model. -/
def ModalUniformFitchRecovery
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) : Prop :=
  ∀ (w : W) (phi : ModalFormula Atom Ag),
    w ∈ m.worlds →
    ∀ w', w' ∈ m.R i w →
      ModalFitchLocalPackageAt m i w' phi

/-- Source-side bridge from a positively true but positively unknown formula to
positive support for the internal Moorean conjunction. -/
theorem modal_moore_positive_of_truth_unknown_no_gap
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hTrue : modalPositiveAt m w phi)
    (hUnknown : modalLacksPositiveKnowledgeAt m i w phi)
    (hNoGap : ModalKnowledgeNoGapAt m i w phi) :
    modalPositiveAt m w (modalMooreFormula i phi) := by
  have hNeg : modalNegativeKnowledgeAt m i w phi :=
    hNoGap hUnknown
  unfold modalPositiveAt modalMooreFormula
  change ((evalModal m w phi).pos &&
    (evalModal m w (ModalFormula.know i phi)).neg) = true
  rw [hTrue, hNeg]

/-- Positive Church--Fitch collapse theorem.

If every positively true modal formula is positively raw-knowable, if source
points have no knowledge gaps of the kind needed to turn meta-level unknownness
into internal `not K`, and if every accessible positive knowledge witness obeys
the previously verified local recovery package, then every positively true
formula is positively known.

The theorem is intentionally about positive/designated truth and positive
knowledge.  It does not identify those notions with strict `T`. -/
theorem church_fitch_positive_omniscience_of_knowability
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hKnowability : ModalPositiveKnowabilityPrinciple m i)
    (hNoGap : ∀ (w : W) (phi : ModalFormula Atom Ag),
      w ∈ m.worlds → ModalKnowledgeNoGapAt m i w phi)
    (hRecovery : ModalUniformFitchRecovery m i) :
    ModalPositiveOmniscience m i := by
  intro w phi hw hTrue
  unfold modalPositiveKnownAt
  cases hK : (evalModal m w (ModalFormula.know i phi)).pos with
  | true =>
      exact hK
  | false =>
      have hUnknown : modalLacksPositiveKnowledgeAt m i w phi := hK
      have hMoore : modalPositiveAt m w (modalMooreFormula i phi) :=
        modal_moore_positive_of_truth_unknown_no_gap
          m i w phi hTrue hUnknown (hNoGap w phi hw)
      have hKnowableMoore :
          modalPositiveKnowableAt m i w (modalMooreFormula i phi) :=
        hKnowability w (modalMooreFormula i phi) hw hMoore
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

/-- Equivalent contrapositive reading at the schema level: if positive
omniscience fails while the source no-gap bridge and uniform witness recovery
hold, then the positive knowability principle must fail. -/
theorem church_fitch_failure_of_knowability_of_non_omniscience
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag)
    (hNoGap : ∀ (w : W) (phi : ModalFormula Atom Ag),
      w ∈ m.worlds → ModalKnowledgeNoGapAt m i w phi)
    (hRecovery : ModalUniformFitchRecovery m i)
    (hNotOmniscient : ¬ ModalPositiveOmniscience m i) :
    ¬ ModalPositiveKnowabilityPrinciple m i := by
  intro hKnowability
  exact hNotOmniscient
    (church_fitch_positive_omniscience_of_knowability
      m i hKnowability hNoGap hRecovery)

/-!
## Interpretation

The positive Church--Fitch theorem now decomposes into four structurally
separate transports:

1. source no-gap: lack of positive `K phi` yields internal `not K phi`;
2. positive knowability: the Moorean truth yields raw possibility of knowing it;
3. witness stability/reflexivity: knowledge of the Moorean conjunction restores
   the classical collision locally;
4. witness no-glut: the collision is made impossible rather than tolerated as
   a four-valued glut.

The preceding independence module already shows that each member of the
witness-side triple is locally irredundant relative to the other two.  Future
work should test the source-side no-gap bridge for independence as well and then
compare positive/designated versus strict-`T` Church--Fitch schemas.
-/

end PEL4
