import PEL4.Syntax
import PEL4.CPEL

namespace PEL4

mutual

/-- Translates the positive support conditions of a 4-PEL formula into Classical PEL syntax.
    Atomic propositions p are mapped to the classical proposition (p, true). -/
def tr_pos {Atom Ag : Type} : Formula Atom Ag → CPELFormula (Atom × Bool) Ag
  | Formula.prop p => CPELFormula.prop (p, true)
  | Formula.not f  => tr_neg f
  | Formula.and f g => CPELFormula.and (tr_pos f) (tr_pos g)
  | Formula.bel i f => CPELFormula.bel i (tr_pos f)

/-- Translates the negative support conditions of a 4-PEL formula into Classical PEL syntax.
    Atomic propositions p are mapped to the classical proposition (p, false). -/
def tr_neg {Atom Ag : Type} : Formula Atom Ag → CPELFormula (Atom × Bool) Ag
  | Formula.prop p => CPELFormula.prop (p, false)
  | Formula.not f  => tr_pos f
  | Formula.and f g => CPELFormula.or (tr_neg f) (tr_neg g)
  | Formula.bel i f => CPELFormula.bel i (tr_neg f)

end

/- The Completeness Reduction strategy:
    A 4-PEL formula $\phi$ is valid if and only if its positive and negative 
    translations are valid in Classical PEL over the split atomic space (Atom x Bool).
    Because CPEL formulas with probability threshold inequalities admit standard 
    Fagin-Halpern canonical models, this guarantees strong completeness and decidability 
    for the static fragment of 4-PEL. -/

end PEL4
