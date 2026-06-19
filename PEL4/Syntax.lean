import PEL4.Belief

namespace PEL4

/-- The abstract syntax of 4-PEL formulas. -/
inductive Formula (Atom Ag : Type) where
  | prop : Atom → Formula Atom Ag
  | not  : Formula Atom Ag → Formula Atom Ag
  | and  : Formula Atom Ag → Formula Atom Ag → Formula Atom Ag
  | bel  : Ag → Formula Atom Ag → Formula Atom Ag

/-- Evaluate a formula in a model at a specific world. -/
def eval {W Ag Atom : Type} [DecidableEq W] (m : Model W Ag Atom) : W → Formula Atom Ag → FDEValue
| w, Formula.prop p => m.val w p
| w, Formula.not f => FDEValue.not (eval m w f)
| w, Formula.and f g => FDEValue.and (eval m w f) (eval m w g)
| w, Formula.bel i f => belief m i w (fun w' => eval m w' f)

/-- Strict-Tolerant (ST) Entailment: phi ⊢_ST psi -/
inductive ST_Entails {Atom Ag : Type} : Formula Atom Ag → Formula Atom Ag → Type where
  | id : ∀ (phi : Formula Atom Ag), ST_Entails phi phi
  -- In ST, Modus Ponens (or equivalent classical rules) holds, but we'll keep it simple for the prototype
  | double_neg_elim : ∀ (phi : Formula Atom Ag), ST_Entails (Formula.not (Formula.not phi)) phi
  | double_neg_intro : ∀ (phi : Formula Atom Ag), ST_Entails phi (Formula.not (Formula.not phi))
  | and_elim_l : ∀ (phi psi : Formula Atom Ag), ST_Entails (Formula.and phi psi) phi
  | and_elim_r : ∀ (phi psi : Formula Atom Ag), ST_Entails (Formula.and phi psi) psi

end PEL4
