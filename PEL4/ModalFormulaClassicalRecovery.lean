import PEL4.FormulaClassicalRecovery
import PEL4.ModalLanguage

namespace PEL4

/-!
# Gate 6: modal preservation of the recovered classical sector

The Lockean belief operator can reopen a gap even when every atomic input value is
classical. This file tests the other two primitive modal transports. The key input
condition is semantic: every value on the relevant accessible list is already in the
`{T,F}` slice.
-/

/-- On the classical slice, the negative bit is the Boolean complement of the
positive bit. -/
theorem classicalValue_neg_eq_not_pos
    (v : FDEValue)
    (h : IsClassicalValue v) :
    v.neg = !v.pos := by
  rcases h with h | h
  · subst v
    rfl
  · subst v
    rfl

/-- For a classical-valued finite profile, all worlds are negatively supported
exactly when no world is positively supported. -/
theorem list_all_neg_eq_not_any_pos
    {W : Type}
    (S : List W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ S → IsClassicalValue (value u)) :
    S.all (fun u => (value u).neg) =
      !(S.any (fun u => (value u).pos)) := by
  induction S with
  | nil =>
      rfl
  | cons a rest ih =>
      have ha : (value a).neg = !(value a).pos :=
        classicalValue_neg_eq_not_pos (value a)
          (hClassical a (by simp))
      have hrest : ∀ u, u ∈ rest → IsClassicalValue (value u) := by
        intro u hu
        exact hClassical u (by simp [hu])
      have hih := ih hrest
      simp only [List.all_cons, List.any_cons]
      rw [ha, hih]
      cases hpa : (value a).pos <;>
        cases hpr : rest.any (fun u => (value u).pos) <;>
        simp [hpa, hpr]

/-- Dually, some accessible world is negatively supported exactly when not all
accessible worlds are positively supported. -/
theorem list_any_neg_eq_not_all_pos
    {W : Type}
    (S : List W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ S → IsClassicalValue (value u)) :
    S.any (fun u => (value u).neg) =
      !(S.all (fun u => (value u).pos)) := by
  induction S with
  | nil =>
      rfl
  | cons a rest ih =>
      have ha : (value a).neg = !(value a).pos :=
        classicalValue_neg_eq_not_pos (value a)
          (hClassical a (by simp))
      have hrest : ∀ u, u ∈ rest → IsClassicalValue (value u) := by
        intro u hu
        exact hClassical u (by simp [hu])
      have hih := ih hrest
      simp only [List.any_cons, List.all_cons]
      rw [ha, hih]
      cases hpa : (value a).pos <;>
        cases hpr : rest.all (fun u => (value u).pos) <;>
        simp [hpa, hpr]

/-- Raw accessibility possibility preserves the classical slice whenever every
accessible input value is classical. Empty accessibility is included and yields F. -/
theorem modalRawPossibilityValue_classical_of_profile
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag) (w : W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ m.R i w → IsClassicalValue (value u)) :
    IsClassicalValue (modalRawPossibilityValue m i w value) := by
  have hrel :=
    list_all_neg_eq_not_any_pos (m.R i w) value hClassical
  unfold modalRawPossibilityValue
  rw [hrel]
  cases hp : (m.R i w).any (fun u => (value u).pos) <;>
    simp [hp, IsClassicalValue, FDEValue.T, FDEValue.F]

/-- Evidence-stable knowledge also preserves the classical slice on a classical
accessible profile. If the profile is unstable, the operator collapses to F; if it
is stable, the common T/F value is retained. -/
theorem modalKnowledgeValue_classical_of_profile
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (i : Ag) (w : W)
    (value : W → FDEValue)
    (hClassical : ∀ u, u ∈ m.R i w → IsClassicalValue (value u)) :
    IsClassicalValue (modalKnowledgeValue m i w value) := by
  have hrel :=
    list_any_neg_eq_not_all_pos (m.R i w) value hClassical
  unfold modalKnowledgeValue
  rw [hrel]
  cases hs : modalAccessibleValueStable (m.R i w) value <;>
    cases hp : (m.R i w).all (fun u => (value u).pos) <;>
    simp [hs, hp, IsClassicalValue, FDEValue.T, FDEValue.F]

/-- Modal formulas that contain no Lockean belief constructor. Knowledge and raw
possibility are retained because Gate 6 proves them classicality-preserving. -/
inductive ModalFormula.IsBeliefFree {Atom Ag : Type} :
    ModalFormula Atom Ag → Prop where
  | prop (p : Atom) :
      ModalFormula.IsBeliefFree (ModalFormula.prop p)
  | not {phi : ModalFormula Atom Ag} :
      ModalFormula.IsBeliefFree phi →
      ModalFormula.IsBeliefFree (ModalFormula.not phi)
  | and {phi psi : ModalFormula Atom Ag} :
      ModalFormula.IsBeliefFree phi →
      ModalFormula.IsBeliefFree psi →
      ModalFormula.IsBeliefFree (ModalFormula.and phi psi)
  | know (i : Ag) {phi : ModalFormula Atom Ag} :
      ModalFormula.IsBeliefFree phi →
      ModalFormula.IsBeliefFree (ModalFormula.know i phi)
  | poss (i : Ag) {phi : ModalFormula Atom Ag} :
      ModalFormula.IsBeliefFree phi →
      ModalFormula.IsBeliefFree (ModalFormula.poss i phi)

/-- Strong Gate-6 modal lift: if every atom is T/F at every world, then every
belief-free modal formula is T/F at every world. -/
theorem evalModal_isClassical_of_beliefFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hAtoms : AtomicClassicalModel m)
    {phi : ModalFormula Atom Ag}
    (hphi : ModalFormula.IsBeliefFree phi) :
    ∀ w, IsClassicalValue (evalModal m w phi) := by
  induction hphi with
  | prop p =>
      intro w
      exact hAtoms w p
  | not h ih =>
      intro w
      exact classicalValue_not _ (ih w)
  | and hphi hpsi ihPhi ihPsi =>
      intro w
      exact classicalValue_and _ _ (ihPhi w) (ihPsi w)
  | know i h ih =>
      intro w
      apply modalKnowledgeValue_classical_of_profile m i w
        (fun u => evalModal m u _)
      intro u hu
      exact ih u
  | poss i h ih =>
      intro w
      apply modalRawPossibilityValue_classical_of_profile m i w
        (fun u => evalModal m u _)
      intro u hu
      exact ih u

end PEL4
