import PEL4.SantosDynamics

namespace PEL4

/-!
# Santos bridge: formula-level reduction (S1) and the two updates

* **S1.** Conditionalisation changes only the measure, so the value of a formula is
  invariant exactly as far as it does not consult the measure: every belief-free
  formula keeps its value (`eval_conditionalize_of_beliefFree`).  Belief formulas do
  not: announcing `p` can turn `B p` from `F` into `T` (`bel_not_invariant`).  For
  belief of a belief-free formula the reduction to a conditional neighbourhood holds
  at the level of formulas (`eval_bel_conditionalize_pos_iff`).
* **The Santos update inside 4-PEL.** Santos' announcement deletes the states that do
  not support the announced formula.  The 4-PEL counterpart `announce` restricts the
  accessible range to `E⁺` and conditionalises the measure.  It is a legal `Model`
  as soon as the evidence has nonzero mass, it yields the *same* Lockean belief as
  conditionalisation in both channels (`belief_announce_eq_conditionalize`), but a
  different relational box: conditionalisation keeps null worlds accessible
  (`box_announce_ne_conditionalize`).
-/

/-- A formula without belief operators. -/
def Formula.beliefFree {Atom Ag : Type} : Formula Atom Ag → Bool
  | Formula.prop _ => true
  | Formula.not f => f.beliefFree
  | Formula.and f g => f.beliefFree && g.beliefFree
  | Formula.bel _ _ => false

/-- **S1, invariance**: belief-free formulas keep their value under conditionalisation. -/
theorem eval_conditionalize_of_beliefFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) (h : ConditionalizationAdmissible m E)
    (phi : Formula Atom Ag) (hf : phi.beliefFree = true) (w : W) :
    eval (conditionalize m E h) w phi = eval m w phi := by
  induction phi generalizing w with
  | prop p => rfl
  | not f ih => simp [eval, ih (by simpa [Formula.beliefFree] using hf)]
  | and f g ihf ihg =>
    have hfg : f.beliefFree = true ∧ g.beliefFree = true := by
      simpa [Formula.beliefFree] using hf
    simp [eval, ihf hfg.1, ihg hfg.2]
  | bel i f _ => simp [Formula.beliefFree] at hf

/-- **S1, reduction at depth one**: for belief-free `φ`, support of `B φ` after the
update is a conditional neighbourhood statement about `‖φ‖⁺` before the update. -/
theorem eval_bel_conditionalize_pos_iff
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) (h : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : Formula Atom Ag) (hf : phi.beliefFree = true)
    (hpos : 0 < conditionalizationEvidenceMass m i w E) :
    (eval (conditionalize m E h) w (Formula.bel i phi)).pos = true ↔
      ConditionalNeighbourhood m i w E (posExtension m i w (fun u => eval m u phi)) := by
  have hEq : (fun u => eval (conditionalize m E h) u phi) = (fun u => eval m u phi) :=
    funext (fun u => eval_conditionalize_of_beliefFree m E h phi hf u)
  simp only [eval, hEq]
  exact belief_conditionalize_pos_iff m E h i w _ hpos

/-- Refutation channel of the depth-one reduction. -/
theorem eval_bel_conditionalize_neg_iff
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) (h : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (phi : Formula Atom Ag) (hf : phi.beliefFree = true)
    (hpos : 0 < conditionalizationEvidenceMass m i w E) :
    (eval (conditionalize m E h) w (Formula.bel i phi)).neg = true ↔
      ConditionalNeighbourhood m i w E (negExtension m i w (fun u => eval m u phi)) := by
  have hEq : (fun u => eval (conditionalize m E h) u phi) = (fun u => eval m u phi) :=
    funext (fun u => eval_conditionalize_of_beliefFree m E h phi hf u)
  simp only [eval, hEq]
  exact belief_conditionalize_neg_iff m E h i w _ hpos

/-! ## The Santos update inside 4-PEL -/

private theorem intersect_self {W : Type} [DecidableEq W] (A : FiniteSet W) :
    intersectWorlds A A = A := by
  unfold intersectWorlds
  exact List.filter_eq_self.mpr (fun u hu => by simpa using hu)

/-- Santos-style announcement: the accessible range shrinks to the worlds supporting
`E`, and the measure is conditionalised.  Nonzero evidence mass is the only proof
obligation. -/
def announce {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hmass : ∀ (i : Ag) (w : W), conditionalizationEvidenceMass m i w E ≠ 0) :
    Model W Ag Atom :=
  { m with
    R := fun i w => evidenceExtension m i w E
    mu := fun i w => conditionalize_mu m i w E
    mu_total := by
      intro i w
      have hne := hmass i w
      unfold conditionalizationEvidenceMass at hne
      simp only [conditionalize_mu, evidenceExtension, beq_iff_eq, hne, if_false,
        intersect_self]
      rw [Rat.div_def, Rat.mul_inv_cancel _ hne]
    mu_empty := by
      intro i w
      have hne := hmass i w
      unfold conditionalizationEvidenceMass at hne
      simp only [conditionalize_mu, beq_iff_eq, hne, if_false]
      have h0 : intersectWorlds ([] : FiniteSet W)
          (filterWorlds (m.R i w) fun w' => (eval m w' E).pos) = [] := rfl
      rw [h0, m.mu_empty i w, Rat.div_def, Rat.zero_mul] }

/-- Belief-free formulas keep their value under the Santos update as well. -/
theorem eval_announce_of_beliefFree
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag)
    (hmass : ∀ (i : Ag) (w : W), conditionalizationEvidenceMass m i w E ≠ 0)
    (phi : Formula Atom Ag) (hf : phi.beliefFree = true) (w : W) :
    eval (announce m E hmass) w phi = eval m w phi := by
  induction phi generalizing w with
  | prop p => rfl
  | not f ih => simp [eval, ih (by simpa [Formula.beliefFree] using hf)]
  | and f g ihf ihg =>
    have hfg : f.beliefFree = true ∧ g.beliefFree = true := by
      simpa [Formula.beliefFree] using hf
    simp [eval, ihf hfg.1, ihg hfg.2]
  | bel i f _ => simp [Formula.beliefFree] at hf

private theorem intersect_filter_range {W : Type} [DecidableEq W]
    (R : FiniteSet W) (p e : W → Bool) :
    intersectWorlds (filterWorlds (filterWorlds R e) p) (filterWorlds R e) =
      intersectWorlds (filterWorlds R p) (filterWorlds R e) := by
  unfold intersectWorlds filterWorlds
  simp only [List.filter_filter]
  apply List.filter_congr
  intro u hu
  simp [List.mem_filter, hu]
  cases e u <;> cases p u <;> rfl

/-- **The two updates agree on Lockean belief**, in both channels. -/
theorem belief_announce_eq_conditionalize
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : Formula Atom Ag) (h : ConditionalizationAdmissible m E)
    (i : Ag) (w : W) (value : W → FDEValue) :
    belief (announce m E h.positive_mass) i w value =
      belief (conditionalize m E h) i w value := by
  simp only [belief, announce, conditionalize, conditionalize_mu, evidenceExtension,
    intersect_filter_range]
  rfl

/-! ## Finite witnesses -/

/-- Three equiprobable worlds; `p` is supported at world `0` and refuted elsewhere. -/
def announceModel : Model (Fin 3) Unit Unit :=
  { worlds := [0, 1, 2]
  , R := fun _ _ => [0, 1, 2]
  , mu := fun _ _ => uniform3
  , val := fun u _ => if u = 0 then FDEValue.T else FDEValue.F
  , c := fun _ => 2 / 3
  , mu_total := by intro _ _; simp [uniform3]; grind
  , mu_empty := by intro _ _; simp [uniform3]; grind
  , c_gt_half := by intro _; grind
  , c_le_one := by intro _; grind }

/-- The announced atom. -/
def announceP : Formula Unit Unit := Formula.prop ()

theorem announceP_admissible : ConditionalizationAdmissible announceModel announceP := by
  refine ⟨?_, ?_, ?_⟩ <;> intro _ _ <;>
    simp [conditionalizationEvidenceMass, conditionalize_mu, intersectWorlds, filterWorlds,
      eval, announceP, announceModel, uniform3, FDEValue.T, FDEValue.F] <;> grind

/-- **S1, non-invariance**: conditionalising on `p` turns `B p` from `F` into `T`. -/
theorem bel_not_invariant :
    eval announceModel 0 (Formula.bel () announceP) = FDEValue.F ∧
    eval (conditionalize announceModel announceP announceP_admissible) 0
      (Formula.bel () announceP) = FDEValue.T := by
  refine ⟨?_, ?_⟩ <;>
    simp [eval, belief, conditionalize, conditionalize_mu, intersectWorlds, filterWorlds,
      announceP, announceModel, uniform3, FDEValue.T, FDEValue.F] <;> grind

/-- **The two updates differ on the relational box**: after the Santos update `□p`
is `T`; after conditionalisation the null worlds stay accessible and `□p` is `F`,
although `B p` is `T` in both. -/
theorem box_announce_ne_conditionalize :
    santosBox (announce announceModel announceP announceP_admissible.positive_mass) () 0
        (fun u => announceModel.val u ()) = FDEValue.T ∧
    santosBox (conditionalize announceModel announceP announceP_admissible) () 0
        (fun u => announceModel.val u ()) = FDEValue.F := by
  refine ⟨?_, ?_⟩ <;>
    simp [santosBox, announce, conditionalize, evidenceExtension, filterWorlds, eval,
      announceP, announceModel, FDEValue.T, FDEValue.F]

end PEL4
