import PEL4.Paradoxes.Fitch

namespace PEL4

/-!
# Fitch recovery boundary

`Fitch.lean` gives an object-language witness in which a Moorean truth is raw
knowable and, at a reflexive possible state,

  K+(p and not K p)

holds while `K+(p)` fails.  The failure is caused by instability of the complete
FDE value of `p` across the accessible range.

This module asks the converse question: which additional conditions restore the
local classical Fitch collision?

The answer is deliberately local and small.  From positive knowledge of

  phi and not K phi

we need only:

* reflexivity at the critical point, so knowledge of the compound is factive;
* stability of the left component `phi`, so knowledge-conjunction extraction to
  `K phi` is licensed;
* a no-glut condition for `K phi`, ruling out simultaneous positive and negative
  support for that knowledge claim.

Notably, we do not need to extract `K(not K phi)` from knowledge of the
conjunction.  Reflexive factivity of the compound already yields `not K phi` at
the critical point.
-/

/-- Local non-gluttiness of one object-language knowledge claim.  If `K phi`
has positive support at the point, it must lack negative support there. -/
def ModalKnowledgeNoGlutAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  (evalModal m w (ModalFormula.know i phi)).pos = true →
    (evalModal m w (ModalFormula.know i phi)).neg = false

/-- Positive object-language knowledge decomposes semantically into universal
positive support and full-value stability. -/
theorem modal_positive_knowledge_components
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hK : (evalModal m w (ModalFormula.know i phi)).pos = true) :
    (m.R i w).all (fun w' => (evalModal m w' phi).pos) = true ∧
      modalAccessibleValueStable (m.R i w)
        (fun w' => evalModal m w' phi) = true := by
  simpa [evalModal, modalKnowledgeValue] using hK

/-- Positive knowledge is factive at a reflexive point in the modal object
language. -/
theorem modal_positive_knowledge_factive_at_reflexive_point
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (href : w ∈ m.R i w)
    (hK : (evalModal m w (ModalFormula.know i phi)).pos = true) :
    (evalModal m w phi).pos = true := by
  have hall := (modal_positive_knowledge_components m i w phi hK).1
  have hall' : ∀ x, x ∈ m.R i w → (evalModal m x phi).pos = true := by
    simpa only [List.all_eq_true] using hall
  exact hall' w href

/-- Positive knowledge of a conjunction transports to positive knowledge of its
left component once that component is itself stable across the accessible
range. -/
theorem modal_positive_knowledge_conjunction_left_of_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : ModalFormula Atom Ag)
    (hK : (evalModal m w
      (ModalFormula.know i (ModalFormula.and phi psi))).pos = true)
    (hstable : modalAccessibleValueStable (m.R i w)
      (fun w' => evalModal m w' phi) = true) :
    (evalModal m w (ModalFormula.know i phi)).pos = true := by
  have hallAnd :=
    (modal_positive_knowledge_components m i w
      (ModalFormula.and phi psi) hK).1
  have hallPhi :
      (m.R i w).all (fun w' => (evalModal m w' phi).pos) = true := by
    simp only [List.all_eq_true] at hallAnd ⊢
    intro w' hw'
    have h := hallAnd w' hw'
    change ((evalModal m w' phi).pos && (evalModal m w' psi).pos) = true at h
    cases hp : (evalModal m w' phi).pos <;> simp_all
  simpa [evalModal, modalKnowledgeValue, hallPhi, hstable]

/-- Exact modal left-extraction boundary.  Under positive knowledge of a
conjunction, positive knowledge of the left conjunct is equivalent to stability
of that conjunct. -/
theorem modal_positive_knowledge_conjunction_left_iff_stable
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi psi : ModalFormula Atom Ag)
    (hK : (evalModal m w
      (ModalFormula.know i (ModalFormula.and phi psi))).pos = true) :
    (evalModal m w (ModalFormula.know i phi)).pos = true ↔
      modalAccessibleValueStable (m.R i w)
        (fun w' => evalModal m w' phi) = true := by
  constructor
  · intro hKphi
    exact (modal_positive_knowledge_components m i w phi hKphi).2
  · intro hstable
    exact modal_positive_knowledge_conjunction_left_of_stable
      m i w phi psi hK hstable

/-- Minimal local Fitch collision theorem.

At a reflexive point, positive knowledge of `phi and not K phi`, together with
stability of `phi`, yields positive `K phi` by the exact conjunction boundary.
Factivity of knowledge of the compound yields `not K phi`, i.e. negative support
for `K phi`.  A local no-glut condition on `K phi` therefore makes the package
inconsistent.
-/
theorem local_fitch_collapse_of_stability_reflexivity_no_glut
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (href : w ∈ m.R i w)
    (hKMoore : (evalModal m w
      (ModalFormula.know i
        (ModalFormula.and phi
          (ModalFormula.not (ModalFormula.know i phi))))).pos = true)
    (hstable : modalAccessibleValueStable (m.R i w)
      (fun w' => evalModal m w' phi) = true)
    (hNoGlut : ModalKnowledgeNoGlutAt m i w phi) :
    False := by
  have hKphi :
      (evalModal m w (ModalFormula.know i phi)).pos = true := by
    exact modal_positive_knowledge_conjunction_left_of_stable
      m i w phi (ModalFormula.not (ModalFormula.know i phi))
      hKMoore hstable
  have hMoore :
      (evalModal m w
        (ModalFormula.and phi
          (ModalFormula.not (ModalFormula.know i phi)))).pos = true := by
    exact modal_positive_knowledge_factive_at_reflexive_point
      m i w
      (ModalFormula.and phi
        (ModalFormula.not (ModalFormula.know i phi)))
      href hKMoore
  have hKphiNeg :
      (evalModal m w (ModalFormula.know i phi)).neg = true := by
    change ((evalModal m w phi).pos &&
      (evalModal m w (ModalFormula.know i phi)).neg) = true at hMoore
    cases hn : (evalModal m w (ModalFormula.know i phi)).neg <;> simp_all
  have hKphiNegFalse := hNoGlut hKphi
  simp [hKphiNeg] at hKphiNegFalse

/-- The verified Fitch countermodel already satisfies reflexivity and local
non-gluttiness of `K p`; it evades the recovery theorem specifically because
`p` is unstable across the critical accessible cluster. -/
theorem fitch_witness_violates_exactly_left_stability_in_local_package :
    FitchWorld.witness ∈ FitchModel.R FitchAgent.a FitchWorld.witness ∧
    ModalKnowledgeNoGlutAt FitchModel FitchAgent.a FitchWorld.witness fitchP ∧
    modalAccessibleValueStable
        (FitchModel.R FitchAgent.a FitchWorld.witness)
        (fun w' => evalModal FitchModel w' fitchP) = false := by
  native_decide

/-!
## Interpretation

The local Fitch boundary is therefore sharper than a generic appeal to
paraconsistency.

The countermodel does not escape because the critical point is non-reflexive: it
is reflexive.  Nor does it escape because `K p` is already glutty: there it is
strictly `F`.  What blocks the classical extraction is precisely the instability
of `p` across the worlds relevant to knowledge.

Conversely, adding component stability restores `K p`.  Reflexive factivity of
`K(p and not K p)` simultaneously restores `not K p`.  Only then does a
no-glut constraint convert the resulting four-valued collision into
impossibility.

This gives a candidate minimal local package for the classical Fitch reductio:

  reflexivity + component stability + knowledge no-glut.

The next gate can lift this local theorem through primitive raw possibility and
state a global knowability-collapse result with the required frame/stability
conditions made explicit.
-/

end PEL4
