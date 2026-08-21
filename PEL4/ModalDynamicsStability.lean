import PEL4.Dynamics
import PEL4.ModalKnowledgePositiveNecessitation

namespace PEL4

/-!
# Dynamic stability under probabilistic conditionalization

Safe conditionalization changes only the local probability measure `mu` of a
4-PEL model.  It leaves the explicit world list, accessibility relation,
valuation, and threshold unchanged.

The modal language therefore has a sharp syntactic dynamic boundary.  Formulas
that contain no probabilistic belief operator `bel` are insensitive to
conditionalization: their complete FDE values are unchanged at every world.
Because their values and accessibility ranges are unchanged, their accessible
full-value stability and all outer `K`/raw-possibility values are preserved as
well.

This does not say that conditionalization is dynamically trivial.  Formulas
containing `bel` can change value, as the verified Surprise trajectory already
shows.  The theorem isolates exactly where probability update can enter the
modal evaluator.
-/

/-- A modal formula is probability-free when it contains no `bel` constructor.
Knowledge and raw possibility are allowed recursively because their semantics
use only accessibility and the values of their subformulas. -/
inductive ModalProbabilityFree {Atom Ag : Type} :
    ModalFormula Atom Ag → Prop where
  | prop (p : Atom) : ModalProbabilityFree (ModalFormula.prop p)
  | neg {phi : ModalFormula Atom Ag} :
      ModalProbabilityFree phi →
      ModalProbabilityFree (ModalFormula.not phi)
  | conj {phi psi : ModalFormula Atom Ag} :
      ModalProbabilityFree phi →
      ModalProbabilityFree psi →
      ModalProbabilityFree (ModalFormula.and phi psi)
  | know (i : Ag) {phi : ModalFormula Atom Ag} :
      ModalProbabilityFree phi →
      ModalProbabilityFree (ModalFormula.know i phi)
  | poss (i : Ag) {phi : ModalFormula Atom Ag} :
      ModalProbabilityFree phi →
      ModalProbabilityFree (ModalFormula.poss i phi)

/-- Conditionalization leaves accessibility unchanged. -/
theorem conditionalize_accessibility_eq
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) :
    (conditionalize m E hAdm).R i w = m.R i w := by
  rfl

/-- Knowledge depends on the model only through the local accessibility range
once the interpreted value function is fixed. -/
theorem modalKnowledgeValue_congr
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom) (i : Ag) (w : W)
    (vM vN : W → FDEValue)
    (hR : n.R i w = m.R i w)
    (hV : vN = vM) :
    modalKnowledgeValue n i w vN = modalKnowledgeValue m i w vM := by
  unfold modalKnowledgeValue
  rw [hR, hV]

/-- Raw possibility likewise depends only on accessibility and the interpreted
value function. -/
theorem modalRawPossibilityValue_congr
    {W Ag Atom : Type} [DecidableEq W]
    (m n : Model W Ag Atom) (i : Ag) (w : W)
    (vM vN : W → FDEValue)
    (hR : n.R i w = m.R i w)
    (hV : vN = vM) :
    modalRawPossibilityValue n i w vN =
      modalRawPossibilityValue m i w vM := by
  unfold modalRawPossibilityValue
  rw [hR, hV]

/-- Conditionalization preserves the complete FDE value of every
probability-free modal formula at every world. -/
theorem evalModal_conditionalize_of_probabilityFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    ∀ w,
      evalModal (conditionalize m E hAdm) w phi =
        evalModal m w phi := by
  induction hFree with
  | prop p =>
      intro w
      rfl
  | neg hPhi ih =>
      intro w
      change FDEValue.not
          (evalModal (conditionalize m E hAdm) w _) =
        FDEValue.not (evalModal m w _)
      rw [ih w]
  | conj hPhi hPsi ihPhi ihPsi =>
      intro w
      change FDEValue.and
          (evalModal (conditionalize m E hAdm) w _)
          (evalModal (conditionalize m E hAdm) w _) =
        FDEValue.and (evalModal m w _) (evalModal m w _)
      rw [ihPhi w, ihPsi w]
  | @know i phi hPhi ih =>
      intro w
      change modalKnowledgeValue (conditionalize m E hAdm) i w
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
        modalKnowledgeValue m i w (fun u => evalModal m u phi)
      have hValues :
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact ih u
      exact modalKnowledgeValue_congr
        m (conditionalize m E hAdm) i w
        (fun u => evalModal m u phi)
        (fun u => evalModal (conditionalize m E hAdm) u phi)
        (conditionalize_accessibility_eq m E hAdm i w) hValues
  | @poss i phi hPhi ih =>
      intro w
      change modalRawPossibilityValue (conditionalize m E hAdm) i w
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
        modalRawPossibilityValue m i w (fun u => evalModal m u phi)
      have hValues :
          (fun u => evalModal (conditionalize m E hAdm) u phi) =
            (fun u => evalModal m u phi) := by
        funext u
        exact ih u
      exact modalRawPossibilityValue_congr
        m (conditionalize m E hAdm) i w
        (fun u => evalModal m u phi)
        (fun u => evalModal (conditionalize m E hAdm) u phi)
        (conditionalize_accessibility_eq m E hAdm i w) hValues

/-- Accessible full-value stability of a probability-free formula is invariant
under admissible probabilistic conditionalization. -/
theorem modal_stability_conditionalize_of_probabilityFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    modalAccessibleValueStable
        ((conditionalize m E hAdm).R i w)
        (fun u => evalModal (conditionalize m E hAdm) u phi) =
      modalAccessibleValueStable
        (m.R i w)
        (fun u => evalModal m u phi) := by
  have hValues :
      (fun u => evalModal (conditionalize m E hAdm) u phi) =
        (fun u => evalModal m u phi) := by
    funext u
    exact evalModal_conditionalize_of_probabilityFree
      m E hAdm hFree u
  rw [conditionalize_accessibility_eq m E hAdm i w, hValues]

/-- In particular, knowledge of a probability-free formula has exactly the
same complete FDE value before and after conditionalization. -/
theorem modal_knowledge_conditionalize_of_probabilityFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    evalModal (conditionalize m E hAdm) w (ModalFormula.know i phi) =
      evalModal m w (ModalFormula.know i phi) := by
  exact evalModal_conditionalize_of_probabilityFree
    m E hAdm (ModalProbabilityFree.know i hFree) w

/-- Raw accessibility possibility of a probability-free formula is likewise
invariant under probabilistic conditionalization. -/
theorem modal_possibility_conditionalize_of_probabilityFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (i : Ag) (w : W)
    {phi : ModalFormula Atom Ag}
    (hFree : ModalProbabilityFree phi) :
    evalModal (conditionalize m E hAdm) w (ModalFormula.poss i phi) =
      evalModal m w (ModalFormula.poss i phi) := by
  exact evalModal_conditionalize_of_probabilityFree
    m E hAdm (ModalProbabilityFree.poss i hFree) w

/-!
## Interpretation

For the current update operator:

```text
conditionalization changes mu only.
```

Hence the modal language splits into two dynamic sectors:

```text
probability-free fragment -> complete FDE value invariant
contains bel              -> may change under update.
```

The first sector includes arbitrarily nested `K` and raw possibility as long as
no probabilistic belief subformula occurs.  Its full-value stability is therefore
an update invariant.

This gives a precise first answer to the dynamic-stability question: ordinary
probabilistic conditionalization cannot by itself create or destroy epistemic
instability in a formula whose semantics never reads the probability measure.
Any such change must be mediated by a `bel` occurrence, or by a future update
operator that also changes accessibility or valuation.
-/

end PEL4
