import PEL4.Belief

namespace PEL4

/-- The abstract syntax of Classical Probabilistic Epistemic Logic (CPEL).
    This serves as the translation target for the completeness reduction. -/
inductive CPELFormula (Atom Ag : Type) where
  | prop : Atom → CPELFormula Atom Ag
  | not  : CPELFormula Atom Ag → CPELFormula Atom Ag
  | and  : CPELFormula Atom Ag → CPELFormula Atom Ag → CPELFormula Atom Ag
  | bel  : Ag → CPELFormula Atom Ag → CPELFormula Atom Ag

/-- Syntactic macro for OR (Disjunction) via De Morgan in classical syntax. -/
def CPELFormula.or {Atom Ag : Type} (phi psi : CPELFormula Atom Ag) : CPELFormula Atom Ag :=
  CPELFormula.not (CPELFormula.and (CPELFormula.not phi) (CPELFormula.not psi))

/-- Syntactic macro for IMPLIES (Material Implication) in classical syntax. -/
def CPELFormula.implies {Atom Ag : Type} (phi psi : CPELFormula Atom Ag) : CPELFormula Atom Ag :=
  CPELFormula.or (CPELFormula.not phi) psi

end PEL4
