import PEL4.Paradoxes.FitchRecovery

namespace PEL4

/-!
# Global Fitch knowability boundary

The local recovery theorem shows that a positive instance of

  K(phi and not K phi)

cannot occur at a point that simultaneously satisfies:

* reflexivity,
* accessible full-value stability of `phi`, and
* local non-gluttiness of `K phi`.

This module lifts that local result through primitive raw accessibility
possibility. The resulting boundary says that positive raw knowability of the
Moorean knowledge claim requires at least one accessible positive witness to
escape the local recovery package.
-/

/-- Generic Moorean formula used in the global Fitch gate. -/
def modalMooreFormula {Atom Ag : Type}
    (i : Ag) (phi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.and phi (ModalFormula.not (ModalFormula.know i phi))

/-- Knowledge of the Moorean formula. -/
def modalKnowledgeOfMoore {Atom Ag : Type}
    (i : Ag) (phi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.know i (modalMooreFormula i phi)

/-- Primitive raw knowability of knowledge of the Moorean formula. -/
def modalRawKnowabilityOfMoore {Atom Ag : Type}
    (i : Ag) (phi : ModalFormula Atom Ag) : ModalFormula Atom Ag :=
  ModalFormula.poss i (modalKnowledgeOfMoore i phi)

/-- The local structural package that restores the classical Fitch collision at
one candidate knowledge witness. -/
def ModalFitchLocalPackageAt {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag) : Prop :=
  w ∈ m.R i w ∧
    modalAccessibleValueStable (m.R i w)
      (fun w' => evalModal m w' phi) = true ∧
    ModalKnowledgeNoGlutAt m i w phi

/-- Positive primitive raw possibility always exposes an accessible positive
witness. -/
theorem modal_raw_possibility_positive_has_witness
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hPoss : (evalModal m w (ModalFormula.poss i phi)).pos = true) :
    ∃ w', w' ∈ m.R i w ∧ (evalModal m w' phi).pos = true := by
  simpa [evalModal, modalRawPossibilityValue, List.any_eq_true] using hPoss

/-- Global escape theorem.

If knowledge of the Moorean formula is positively raw-possible, then at least
one accessible positive knowledge witness must violate the local package that
would otherwise force the Fitch collision. -/
theorem raw_fitch_knowability_requires_local_escape
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hPoss : (evalModal m w (modalRawKnowabilityOfMoore i phi)).pos = true) :
    ∃ w',
      w' ∈ m.R i w ∧
      (evalModal m w' (modalKnowledgeOfMoore i phi)).pos = true ∧
      ¬ ModalFitchLocalPackageAt m i w' phi := by
  have hWitness :
      ∃ w', w' ∈ m.R i w ∧
        (evalModal m w' (modalKnowledgeOfMoore i phi)).pos = true := by
    apply modal_raw_possibility_positive_has_witness
      m i w (modalKnowledgeOfMoore i phi)
    simpa [modalRawKnowabilityOfMoore] using hPoss
  rcases hWitness with ⟨w', hw', hKMoore⟩
  refine ⟨w', hw', hKMoore, ?_⟩
  intro hPackage
  have hKMoore' :
      (evalModal m w'
        (ModalFormula.know i
          (ModalFormula.and phi
            (ModalFormula.not (ModalFormula.know i phi))))).pos = true := by
    simpa [modalKnowledgeOfMoore, modalMooreFormula] using hKMoore
  exact local_fitch_collapse_of_stability_reflexivity_no_glut
    m i w' phi hPackage.1 hKMoore' hPackage.2.1 hPackage.2.2

/-- Uniform global collapse theorem.

If every world accessible from the current point satisfies the local recovery
package, then positive raw knowability of the Moorean knowledge claim is
impossible. -/
theorem global_fitch_collapse_of_uniform_local_package
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (hPoss : (evalModal m w (modalRawKnowabilityOfMoore i phi)).pos = true)
    (href : ∀ w', w' ∈ m.R i w → w' ∈ m.R i w')
    (hstable : ∀ w', w' ∈ m.R i w →
      modalAccessibleValueStable (m.R i w')
        (fun u => evalModal m u phi) = true)
    (hNoGlut : ∀ w', w' ∈ m.R i w →
      ModalKnowledgeNoGlutAt m i w' phi) :
    False := by
  rcases raw_fitch_knowability_requires_local_escape
      m i w phi hPoss with
    ⟨w', hw', _, hEscape⟩
  apply hEscape
  exact ⟨href w' hw', hstable w' hw', hNoGlut w' hw'⟩

/-- Equivalent Bool-facing form: under the uniform local recovery package, the
positive component of raw Fitch knowability is false. -/
theorem raw_fitch_knowability_positive_false_of_uniform_local_package
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W)
    (phi : ModalFormula Atom Ag)
    (href : ∀ w', w' ∈ m.R i w → w' ∈ m.R i w')
    (hstable : ∀ w', w' ∈ m.R i w →
      modalAccessibleValueStable (m.R i w')
        (fun u => evalModal m u phi) = true)
    (hNoGlut : ∀ w', w' ∈ m.R i w →
      ModalKnowledgeNoGlutAt m i w' phi) :
    (evalModal m w (modalRawKnowabilityOfMoore i phi)).pos = false := by
  cases hPoss : (evalModal m w (modalRawKnowabilityOfMoore i phi)).pos with
  | false =>
      rfl
  | true =>
      exact False.elim
        (global_fitch_collapse_of_uniform_local_package
          m i w phi hPoss href hstable hNoGlut)

/-!
## Interpretation

The global theorem does not say that paraconsistency by itself blocks Fitch.
It identifies a structural escape requirement.

Positive raw knowability of

  K(phi and not K phi)

requires an accessible positive knowledge witness at which the local classical
recovery package fails. Thus a surviving Fitch witness must exploit at least
one of the following resources:

* non-reflexivity at the witness,
* instability of the full FDE value of `phi` across the witness's epistemic
  alternatives,
* permission for `K phi` itself to be glutty.

The verified finite Fitch model developed in `Fitch.lean` and
`FitchRecovery.lean` realizes the second route: its critical witness is
reflexive and `K p` is non-glutty there, while `p` is unstable across the
relevant accessible cluster.

This is a global knowability boundary, not yet the full Church-Fitch theorem.
A full theorem schema still requires a formal notion of truth-validity and a
knowability principle quantified over formulas or designated truths.
-/

end PEL4
