import PEL4.ConditionalBelief

namespace PEL4

/-!
# Conservativity over the relational four-valued box logic

The belief-free fragment of the extended language (`prop`, `not`, `and`, `box`) is
evaluated on a *relational* model: accessible ranges and a four-valued valuation, no
measure.  Every 4-PEL model has such a reduct, and its ranges are nonempty (serial).
Conversely every serial relational model expands to a 4-PEL model by putting the
uniform counting measure on each range.  Box formulas have the same value in a model
and in its reduct.  Hence a box formula is valid over all 4-PEL models iff it is valid
over all serial relational models with finite ranges: adding Lockean belief is
conservative over that logic.

Scope: seriality and finiteness of ranges are built into 4-PEL (`μ(R) = 1`, list
ranges); the statement is relative to the box clauses of `santosBox`.
-/

/-- Belief-free formulas with the relational box. -/
inductive BFormula (Atom Ag : Type) where
  | prop : Atom → BFormula Atom Ag
  | not  : BFormula Atom Ag → BFormula Atom Ag
  | and  : BFormula Atom Ag → BFormula Atom Ag → BFormula Atom Ag
  | box  : Ag → BFormula Atom Ag → BFormula Atom Ag

/-- Embedding into the extended 4-PEL language. -/
def BFormula.toC {Atom Ag : Type} : BFormula Atom Ag → CFormula Atom Ag
  | BFormula.prop p => CFormula.prop p
  | BFormula.not f => CFormula.not f.toC
  | BFormula.and f g => CFormula.and f.toC g.toC
  | BFormula.box i f => CFormula.box i f.toC

/-- A relational four-valued model with finite accessible ranges. -/
structure RelModel (W Ag Atom : Type) where
  R : Ag → W → FiniteSet W
  val : W → Atom → FDEValue

/-- Every accessible range is nonempty. -/
def RelModel.Serial {W Ag Atom : Type} (s : RelModel W Ag Atom) : Prop :=
  ∀ (i : Ag) (w : W), s.R i w ≠ []

/-- Relational evaluation of box formulas. -/
def evalR {W Ag Atom : Type} (s : RelModel W Ag Atom) : W → BFormula Atom Ag → FDEValue
  | w, BFormula.prop p => s.val w p
  | w, BFormula.not f => FDEValue.not (evalR s w f)
  | w, BFormula.and f g => FDEValue.and (evalR s w f) (evalR s w g)
  | w, BFormula.box i f =>
      { pos := (s.R i w).all (fun u => (evalR s u f).pos)
      , neg := (s.R i w).any (fun u => (evalR s u f).neg) }

/-- The relational reduct of a 4-PEL model. -/
def Model.reduct {W Ag Atom : Type} [DecidableEq W] (m : Model W Ag Atom) :
    RelModel W Ag Atom :=
  { R := m.R, val := m.val }

/-- 4-PEL models are serial: a range of total mass one cannot be empty. -/
theorem Model.reduct_serial {W Ag Atom : Type} [DecidableEq W] (m : Model W Ag Atom) :
    m.reduct.Serial := by
  intro i w h
  have h1 := m.mu_total i w
  have h0 := m.mu_empty i w
  have hR : m.R i w = [] := h
  rw [hR, h0] at h1
  exact absurd h1 (by decide)

/-- Box formulas do not see the measure. -/
theorem evalC_toC_eq_evalR {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (phi : BFormula Atom Ag) (w : W) :
    evalC m w phi.toC = evalR m.reduct w phi := by
  induction phi generalizing w with
  | prop p => rfl
  | not f ih => simp [evalC, evalR, BFormula.toC, ih]
  | and f g ihf ihg => simp [evalC, evalR, BFormula.toC, ihf, ihg]
  | box i f ih =>
    simp only [evalC, evalR, BFormula.toC, santosBox, ih]
    rfl

/-- Uniform expansion of a serial relational model to a 4-PEL model. -/
def RelModel.expand {W Ag Atom : Type} [DecidableEq W]
    (s : RelModel W Ag Atom) (hs : s.Serial) : Model W Ag Atom :=
  { worlds := []
  , R := s.R
  , mu := fun i w X => ((intersectWorlds X (s.R i w)).length : Rat) / ((s.R i w).length : Rat)
  , val := s.val
  , c := fun _ => 1
  , mu_total := by
      intro i w
      have hself : intersectWorlds (s.R i w) (s.R i w) = s.R i w := by
        unfold intersectWorlds
        exact List.filter_eq_self.mpr (fun u hu => by simpa using hu)
      have hlen : ((s.R i w).length : Rat) ≠ 0 := by
        have : (s.R i w).length ≠ 0 := fun h => hs i w (List.length_eq_zero_iff.mp h)
        exact_mod_cast this
      rw [hself, Rat.div_def, Rat.mul_inv_cancel _ hlen]
  , mu_empty := by
      intro i w
      have h0 : intersectWorlds ([] : FiniteSet W) (s.R i w) = [] := rfl
      rw [h0, Rat.div_def]
      simp
  , c_gt_half := by intro _; grind
  , c_le_one := by intro _; grind }

/-- The expansion has the original model as its reduct. -/
theorem RelModel.reduct_expand {W Ag Atom : Type} [DecidableEq W]
    (s : RelModel W Ag Atom) (hs : s.Serial) : (s.expand hs).reduct = s := rfl

/-- **Conservativity, value form**: a box formula has the same value in a serial
relational model and in its 4-PEL expansion. -/
theorem evalC_expand_eq_evalR {W Ag Atom : Type} [DecidableEq W]
    (s : RelModel W Ag Atom) (hs : s.Serial) (phi : BFormula Atom Ag) (w : W) :
    evalC (s.expand hs) w phi.toC = evalR s w phi := by
  rw [evalC_toC_eq_evalR, RelModel.reduct_expand]

/-- **Conservativity, validity form**: for any property of values (support,
non-refutation, a designated set …), a box formula has it at every world of every
4-PEL model iff it has it at every world of every serial relational model. -/
theorem box_validity_conservative {W Ag Atom : Type} [DecidableEq W]
    (D : FDEValue → Prop) (phi : BFormula Atom Ag) :
    (∀ (m : Model W Ag Atom) (w : W), D (evalC m w phi.toC)) ↔
    (∀ (s : RelModel W Ag Atom), s.Serial → ∀ w : W, D (evalR s w phi)) := by
  constructor
  · intro h s hs w
    rw [← evalC_expand_eq_evalR s hs]
    exact h _ w
  · intro h m w
    rw [evalC_toC_eq_evalR]
    exact h _ m.reduct_serial w

end PEL4
