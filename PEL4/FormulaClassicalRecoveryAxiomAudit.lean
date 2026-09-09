import PEL4.FormulaClassicalRecovery
import PEL4.ModalFormulaClassicalRecovery
import PEL4.BeliefClassicalRecovery

/-!
# Gate 6 axiom audit

Selected formula-level recovery, modal preservation, belief recovery, and boundary declarations.
-/

#print axioms PEL4.eval_formula_or
#print axioms PEL4.eval_isClassical_of_propositional
#print axioms PEL4.eval_isClassical_of_atomicClassicalModel
#print axioms PEL4.eval_excludedMiddle_eq_T_of_propositional
#print axioms PEL4.eval_contradiction_eq_F_of_propositional
#print axioms PEL4.propositional_contradiction_LP_valid
#print axioms PEL4.gate6BeliefBoundary_atomicClassical
#print axioms PEL4.gate6BeliefBoundary_belief_is_N
#print axioms PEL4.atomicClassical_does_not_force_belief_classical
#print axioms PEL4.classicalValue_neg_eq_not_pos
#print axioms PEL4.list_all_neg_eq_not_any_pos
#print axioms PEL4.list_any_neg_eq_not_all_pos
#print axioms PEL4.modalRawPossibilityValue_classical_of_profile
#print axioms PEL4.modalKnowledgeValue_classical_of_profile
#print axioms PEL4.evalModal_isClassical_of_beliefFree
#print axioms PEL4.belief_eq_thresholdBits
#print axioms PEL4.belief_isClassical_iff_thresholdRegular
#print axioms PEL4.gate6BeliefBoundary_not_thresholdComplete
#print axioms PEL4.gate6BeliefBoundary_thresholdConsistent
#print axioms PEL4.eval_isClassical_of_recoveryAdmissible
#print axioms PEL4.propositional_recoveryAdmissible
#print axioms PEL4.eval_isClassical_of_global_recoveryAdmissible
