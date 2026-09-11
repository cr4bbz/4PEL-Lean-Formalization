import PEL4.RecoveryScopeStuttering

namespace PEL4

/-!
# Atomic conditionalization idempotence

Gate 29 needs to distinguish a one-step Recovery split from genuine
asymptotic path dependence. For atomic evidence, conditionalization leaves the
truth set of that evidence unchanged. Once conditioned on that event, the event
has posterior mass one, so conditioning on it again is a semantic stutter.
-/

/-- Repeating the same right-hand intersection is list-idempotent. -/
theorem intersectWorlds_repeat_right
    {W : Type} [DecidableEq W]
    (S E : FiniteSet W) :
    intersectWorlds (intersectWorlds S E) E = intersectWorlds S E := by
  apply intersectWorlds_eq_left_of_subset
  exact intersectWorlds_subset_right S E

/-- Atomic evidence has exactly the same positive event before and after any
conditionalization, because `conditionalize` leaves accessibility and atomic
valuation unchanged. -/
theorem conditionalize_prop_event_eq
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m E)
    (p : Atom) (i : Ag) (w : W) :
    filterWorlds ((conditionalize m E hAdm).R i w)
        (fun u => (eval (conditionalize m E hAdm) u (Formula.prop p)).pos) =
      filterWorlds (m.R i w)
        (fun u => (eval m u (Formula.prop p)).pos) := by
  rfl

/-- After one admissible conditioning on atomic evidence `p`, that same event
has posterior mass one. -/
theorem conditionalize_mu_prop_event_eq_one
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (i : Ag) (w : W) :
    conditionalize_mu m i w (Formula.prop p)
        (filterWorlds (m.R i w)
          (fun u => (eval m u (Formula.prop p)).pos)) = 1 := by
  let event := filterWorlds (m.R i w)
    (fun u => (eval m u (Formula.prop p)).pos)
  have hDenNe : m.mu i w event ≠ 0 := by
    simpa [conditionalizationEvidenceMass, event] using hAdm.positive_mass i w
  change conditionalize_mu m i w (Formula.prop p) event = 1
  simp only [conditionalize_mu, beq_iff_eq]
  rw [if_neg hDenNe]
  change m.mu i w (intersectWorlds event event) / m.mu i w event = 1
  rw [intersectWorlds_eq_left_of_subset event event (fun _ hx => hx)]
  rw [Rat.div_def]
  exact Rat.mul_inv_cancel (m.mu i w event) hDenNe

/-- Raw local measures are unchanged by a second conditioning on the same
atomic proposition. -/
theorem conditionalize_mu_repeat_prop_eq
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (i : Ag) (w : W) (S : FiniteSet W) :
    conditionalize_mu (conditionalize m (Formula.prop p) hAdm)
        i w (Formula.prop p) S =
      conditionalize_mu m i w (Formula.prop p) S := by
  let event := filterWorlds (m.R i w)
    (fun u => (eval m u (Formula.prop p)).pos)
  have hDenNe : m.mu i w event ≠ 0 := by
    simpa [conditionalizationEvidenceMass, event] using hAdm.positive_mass i w
  have hEventMass :
      conditionalize_mu m i w (Formula.prop p) event = 1 := by
    simpa [event] using conditionalize_mu_prop_event_eq_one m p hAdm i w
  have hInner :
      conditionalize_mu m i w (Formula.prop p) (intersectWorlds S event) =
        conditionalize_mu m i w (Formula.prop p) S := by
    simp only [conditionalize_mu, beq_iff_eq]
    rw [if_neg hDenNe, if_neg hDenNe]
    change m.mu i w (intersectWorlds (intersectWorlds S event) event) /
          m.mu i w event =
        m.mu i w (intersectWorlds S event) / m.mu i w event
    rw [intersectWorlds_repeat_right]
  change
    (if conditionalize_mu m i w (Formula.prop p) event = 0 then 0
      else conditionalize_mu m i w (Formula.prop p)
          (intersectWorlds S event) /
        conditionalize_mu m i w (Formula.prop p) event) =
      conditionalize_mu m i w (Formula.prop p) S
  rw [hEventMass]
  simp [hInner]

/-- Atomic evidence remains admissible after it has already been learned once. -/
theorem conditionalize_prop_repeat_admissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p)) :
    ConditionalizationAdmissible
      (conditionalize m (Formula.prop p) hAdm) (Formula.prop p) := by
  constructor
  · intro i w
    have hOne := conditionalize_mu_prop_event_eq_one m p hAdm i w
    change conditionalize_mu m i w (Formula.prop p)
      (filterWorlds (m.R i w)
        (fun u => (eval m u (Formula.prop p)).pos)) ≠ 0
    rw [hOne]
    decide
  · intro i w
    change conditionalize_mu (conditionalize m (Formula.prop p) hAdm)
      i w (Formula.prop p) (m.R i w) = 1
    rw [conditionalize_mu_repeat_prop_eq m p hAdm i w (m.R i w)]
    exact hAdm.mu_total i w
  · intro i w
    change conditionalize_mu (conditionalize m (Formula.prop p) hAdm)
      i w (Formula.prop p) [] = 0
    rw [conditionalize_mu_repeat_prop_eq m p hAdm i w []]
    exact hAdm.mu_empty i w

/-- A second atomic update has exactly the same local probability function as
the first updated model. -/
theorem conditionalize_repeat_prop_mu_eq
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (hRepeat := conditionalize_prop_repeat_admissible m p hAdm) :
    (conditionalize (conditionalize m (Formula.prop p) hAdm)
        (Formula.prop p) hRepeat).mu =
      (conditionalize m (Formula.prop p) hAdm).mu := by
  funext i w S
  exact conditionalize_mu_repeat_prop_eq m p hAdm i w S

/-- Full-model idempotence for repeated atomic conditionalization. The proof
uses equality of the only data field changed by conditionalization (`mu`); all
normalization witnesses are propositions and hence proof-irrelevant. -/
theorem conditionalize_repeat_prop_eq
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (hRepeat := conditionalize_prop_repeat_admissible m p hAdm) :
    conditionalize (conditionalize m (Formula.prop p) hAdm)
        (Formula.prop p) hRepeat =
      conditionalize m (Formula.prop p) hAdm := by
  have hMu := conditionalize_repeat_prop_mu_eq m p hAdm hRepeat
  cases m with
  | mk worlds R mu val c hTotal hEmpty hHalf hOne =>
      simp only [conditionalize] at hMu ⊢
      cases hMu
      rfl

end PEL4
