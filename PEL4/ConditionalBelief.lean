import PEL4.SantosReduction

namespace PEL4

/-!
# Conditional belief and the full reduction law

`SantosReduction` settled the reduction of belief under conditionalisation for modal
depth one.  Following the reduction axiom of probabilistic public announcement logic
(Kooi; van Benthem–Gerbrandy–Kooi), `[!A] P(φ) = k ↔ (A → P([!A]φ | A) = k)`, the
static language needs *conditional* belief.  This file adds it in a separate syntax
(the legacy `Formula` is left untouched), together with the relational box, and proves
the reduction for arbitrary modal depth:

  `eval (M ↑ E) φ = eval M (red E φ)`,

where `red E` pushes the update inwards:
`B φ ↦ B(red φ | E)`, `B(φ | ψ) ↦ B(red φ | red ψ ∧ E)`, `□φ ↦ □(red φ)`.

Convention: a condition of mass zero makes the conditional belief trivially supported
and refuted (`0 ≥ c · 0`), i.e. `B`.
-/

/-- Formulas with belief, conditional belief and the relational box. -/
inductive CFormula (Atom Ag : Type) where
  | prop : Atom → CFormula Atom Ag
  | not  : CFormula Atom Ag → CFormula Atom Ag
  | and  : CFormula Atom Ag → CFormula Atom Ag → CFormula Atom Ag
  | bel  : Ag → CFormula Atom Ag → CFormula Atom Ag
  | cbel : Ag → CFormula Atom Ag → CFormula Atom Ag → CFormula Atom Ag
  | box  : Ag → CFormula Atom Ag → CFormula Atom Ag

/-- Conditional Lockean belief `B(v | cond)` on semantic values. -/
def condBelief {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (i : Ag) (w : W) (cond v : W → FDEValue) : FDEValue :=
  let C := filterWorlds (m.R i w) (fun u => (cond u).pos)
  { pos := m.mu i w (intersectWorlds (filterWorlds (m.R i w) (fun u => (v u).pos)) C) ≥
      m.c i * m.mu i w C
  , neg := m.mu i w (intersectWorlds (filterWorlds (m.R i w) (fun u => (v u).neg)) C) ≥
      m.c i * m.mu i w C }

/-- Evaluation of extended formulas.  `cbel i ψ φ` reads `B_i(φ | ψ)`. -/
def evalC {W Ag Atom : Type} [DecidableEq W] (m : Model W Ag Atom) :
    W → CFormula Atom Ag → FDEValue
  | w, CFormula.prop p => m.val w p
  | w, CFormula.not f => FDEValue.not (evalC m w f)
  | w, CFormula.and f g => FDEValue.and (evalC m w f) (evalC m w g)
  | w, CFormula.bel i f => belief m i w (fun u => evalC m u f)
  | w, CFormula.cbel i c f => condBelief m i w (fun u => evalC m u c) (fun u => evalC m u f)
  | w, CFormula.box i f => santosBox m i w (fun u => evalC m u f)

private theorem filter_contains_self {W : Type} [DecidableEq W]
    (R : FiniteSet W) (e : W → Bool) :
    intersectWorlds R (filterWorlds R e) = filterWorlds R e := by
  unfold intersectWorlds filterWorlds
  apply List.filter_congr
  intro u hu
  simp [List.mem_filter, hu]

/-- Conditionalisation of every local measure on the event `{u | e u}`.  Nonzero mass
of the event is the only proof obligation. -/
def condOn {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (e : W → Bool)
    (hmass : ∀ (i : Ag) (w : W), m.mu i w (filterWorlds (m.R i w) e) ≠ 0) :
    Model W Ag Atom :=
  { m with
    mu := fun i w X =>
      m.mu i w (intersectWorlds X (filterWorlds (m.R i w) e)) /
        m.mu i w (filterWorlds (m.R i w) e)
    mu_total := by
      intro i w
      rw [filter_contains_self, Rat.div_def, Rat.mul_inv_cancel _ (hmass i w)]
    mu_empty := by
      intro i w
      have h0 : intersectWorlds ([] : FiniteSet W) (filterWorlds (m.R i w) e) = [] := rfl
      rw [h0, m.mu_empty i w, Rat.div_def, Rat.zero_mul] }

/-- Push a conditionalisation on `E` inside a formula. -/
def red {Atom Ag : Type} (E : CFormula Atom Ag) : CFormula Atom Ag → CFormula Atom Ag
  | CFormula.prop p => CFormula.prop p
  | CFormula.not f => CFormula.not (red E f)
  | CFormula.and f g => CFormula.and (red E f) (red E g)
  | CFormula.bel i f => CFormula.cbel i E (red E f)
  | CFormula.cbel i c f => CFormula.cbel i (CFormula.and (red E c) E) (red E f)
  | CFormula.box i f => CFormula.box i (red E f)

private theorem rat_ge_div_iff (x e c : Rat) (he : 0 < e) : x / e ≥ c ↔ x ≥ c * e := by
  show c ≤ x / e ↔ c * e ≤ x
  constructor
  · intro h
    have := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt he)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt he)] at this
    exact this
  · intro h
    have hi : 0 ≤ e⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr he)
    have := Rat.mul_le_mul_of_nonneg_right h hi
    rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt he), Rat.mul_one] at this
    rw [Rat.div_def]; exact this

private theorem rat_div_ge_mul_div_iff (x y e c : Rat) (he : 0 < e) :
    x / e ≥ c * (y / e) ↔ x ≥ c * y := by
  have h1 : c * (y / e) = (c * y) / e := by
    rw [Rat.div_def, Rat.div_def, Rat.mul_assoc]
  rw [h1]
  show c * y / e ≤ x / e ↔ c * y ≤ x
  rw [show (c * y / e ≤ x / e) = (x / e ≥ c * y / e) from rfl, rat_ge_div_iff _ _ _ he,
    Rat.div_mul_cancel (Rat.ne_of_gt he)]

private theorem intersect_filter_filter {W : Type} [DecidableEq W]
    (R : FiniteSet W) (b e : W → Bool) :
    intersectWorlds (filterWorlds R b) (filterWorlds R e) =
      filterWorlds R (fun u => b u && e u) := by
  unfold intersectWorlds filterWorlds
  rw [List.filter_filter]
  apply List.filter_congr
  intro u hu
  simp [List.mem_filter, hu]
  cases b u <;> cases e u <;> rfl

private theorem intersect_intersect_filter {W : Type} [DecidableEq W]
    (R : FiniteSet W) (a b e : W → Bool) :
    intersectWorlds (intersectWorlds (filterWorlds R a) (filterWorlds R b)) (filterWorlds R e) =
      intersectWorlds (filterWorlds R a) (filterWorlds R (fun u => b u && e u)) := by
  unfold intersectWorlds filterWorlds
  simp only [List.filter_filter]
  apply List.filter_congr
  intro u hu
  simp [List.mem_filter, hu]
  cases a u <;> cases b u <;> cases e u <;> rfl

/-- **Full reduction law.**  For every formula of the extended language, evaluating
after conditionalisation on `E` equals evaluating the reduct before. -/
theorem evalC_condOn_eq_red
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (E : CFormula Atom Ag)
    (hpos : ∀ (i : Ag) (w : W),
      0 < m.mu i w (filterWorlds (m.R i w) (fun u => (evalC m u E).pos)))
    (phi : CFormula Atom Ag) (w : W) :
    evalC (condOn m (fun u => (evalC m u E).pos) (fun i w => Rat.ne_of_gt (hpos i w))) w phi =
      evalC m w (red E phi) := by
  induction phi generalizing w with
  | prop p => rfl
  | not f ih => simp [evalC, red, ih]
  | and f g ihf ihg => simp [evalC, red, ihf, ihg]
  | box i f ih =>
    have hEq : (fun u => evalC (condOn m (fun u => (evalC m u E).pos)
        (fun i w => Rat.ne_of_gt (hpos i w))) u f) = (fun u => evalC m u (red E f)) :=
      funext ih
    simp only [evalC, red, hEq]
    rfl
  | bel i f ih =>
    have hEq : (fun u => evalC (condOn m (fun u => (evalC m u E).pos)
        (fun i w => Rat.ne_of_gt (hpos i w))) u f) = (fun u => evalC m u (red E f)) :=
      funext ih
    simp only [evalC, red, hEq]
    simp only [belief, condBelief, condOn, filterWorlds]
    congr 1 <;> exact decide_eq_decide.mpr (rat_ge_div_iff _ _ _ (hpos i w))
  | cbel i c f ihc ihf =>
    have hEqf : (fun u => evalC (condOn m (fun u => (evalC m u E).pos)
        (fun i w => Rat.ne_of_gt (hpos i w))) u f) = (fun u => evalC m u (red E f)) :=
      funext ihf
    have hEqc : (fun u => evalC (condOn m (fun u => (evalC m u E).pos)
        (fun i w => Rat.ne_of_gt (hpos i w))) u c) = (fun u => evalC m u (red E c)) :=
      funext ihc
    simp only [evalC, red, hEqf, hEqc]
    simp only [condBelief, condOn, FDEValue.and]
    simp only [intersect_filter_filter, Bool.and_assoc]
    congr 1 <;> exact decide_eq_decide.mpr (rat_div_ge_mul_div_iff _ _ _ _ (hpos i w))

end PEL4
