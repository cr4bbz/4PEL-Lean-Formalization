import PEL4.Model
import PEL4.Syntax
import PEL4.Soundness

namespace PEL4

/-- The single world in our counter-model. -/
inductive ExFalsoWorld
  | w1
deriving DecidableEq

/-- The single agent. -/
inductive ExFalsoAgent
  | i

/-- The atomic propositions. -/
inductive ExFalsoAtom
  | p
  | q

open ExFalsoWorld ExFalsoAgent ExFalsoAtom

/-- 
  A concrete 4-PEL model demonstrating that Ex Falso Quodlibet is invalid.
  We set p to be an ontological glut (B), and q to be strictly false (F).
-/
def exFalsoModel : Model ExFalsoWorld ExFalsoAgent ExFalsoAtom where
  worlds := [w1]
  R := fun _ _ => [w1]
  mu := fun _ _ w_list => match w_list with
    | [w1] => 1
    | _ => 0
  val := fun w a => match w, a with
    | w1, p => FDEValue.B
    | w1, q => FDEValue.F
  c := 1
  mu_total := by
    intro _ _
    rfl
  mu_empty := by
    intro _ _
    rfl
  c_gt_half := by
    native_decide
  c_le_one := by
    native_decide

/-- 
  The theorem showing Ex Falso Quodlibet fails under LP-Entailment.
  B_i(p ∧ ¬p) ⊭_LP B_i(q)
-/
theorem ex_falso_invalid : ¬ LP_SemanticEntails 
  (Formula.bel i (Formula.and (Formula.prop p) (Formula.not (Formula.prop p))))
  (Formula.bel i (Formula.prop q)) := by
  intro h
  have h_spec := h exFalsoModel w1
  
  have h_premise : (eval exFalsoModel w1 (Formula.bel i (Formula.and (Formula.prop p) (Formula.not (Formula.prop p))))).pos = true := by
    rfl

  have h_conclusion : (eval exFalsoModel w1 (Formula.bel i (Formula.prop q))).pos = false := by
    rfl

  have h_absurd := h_spec h_premise
  rw [h_conclusion] at h_absurd
  contradiction

end PEL4
