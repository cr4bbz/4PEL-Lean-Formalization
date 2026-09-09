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

/-!
## Intended completeness-reduction strategy

The split translation is designed to represent the positive and negative support
conditions of a 4-PEL formula inside a classical probabilistic epistemic target
language over `(Atom × Bool)`.

Gate 8 proves the semantic bit-correctness of `tr_pos` and `tr_neg` for the explicit
CPEL evaluator in `PEL4.CPELClassicalCollapse`, and proves that the two channels
collapse to Boolean complements on the recovered classical sector.

Those translation theorems are not, by themselves, a strong-completeness or
decidability theorem. A genuine completeness reduction still requires a separately
formalized CPEL model theory, validity notion, and the appropriate canonical-model or
completeness result for that target semantics.
-/

end PEL4
