import PEL4.RecoveryEpistemicAttractor
import PEL4.RecoveryConfluence

namespace PEL4

/-!
# Gate 33: Epistemic hysteresis

Gate 29 showed path dependence under different future evidence choices. Gate 30
then proved that two static atomic conditioning events commute up to complete
modal observational equivalence. Gate 33 asks for the missing history-sensitive
phenomenon: can the same two syntactic evidence ingredients, processed in
opposite orders, lead to different Recovery outcomes?

The answer is yes once one evidence formula is itself belief-dependent. The
positive extension of such evidence can change after the first update, so the
second occurrence of the same formula need not denote the same conditioning
event it would have denoted first.

The concrete witness reuses the Gate-11 instability model. Initially `B p` is
`T/T/T`, so belief-evidence `B p` has the full three-world positive extension.
After learning atomic evidence `e`, the profile becomes `T/N/T`, shrinking the
positive extension of `B p` to `{a,c}`.

Thus:

* `B p ; e` leaves the first step informationally inert and ends in the known
  fractured `T/N/T` posterior;
* `e ; B p` first fractures the profile, then the now smaller positive
  extension of `B p` removes the problematic `b` branch and restores `T/T/T`.

This is order sensitivity with the same syntactic evidence multiset
`{e, B p}`. It is deliberately distinguished from the stronger claim that two
fixed extensional events can exhibit hysteresis: Gate 30 rules that out for the
static atomic subdynamics under probability integrity and mutual sequential
admissibility.
-/

/-- Formula-level belief evidence matching the modal target `B p`. -/
def gate33BelPEvidence :
    Formula DynamicInstabilityAtom DynamicInstabilityAgent :=
  Formula.bel DynamicInstabilityAgent.i
    (Formula.prop DynamicInstabilityAtom.p)

/-- Initially `B p` is positive at all three worlds, so using it as evidence is
admissible everywhere. -/
theorem gate33_belP_initial_admissible :
    ConditionalizationAdmissible
      DynamicInstabilityModel gate33BelPEvidence := by
  constructor
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel

/-- Posterior after processing belief evidence first. -/
def Gate33BelFirst :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize DynamicInstabilityModel gate33BelPEvidence
    gate33_belP_initial_admissible

/-- Static atomic evidence `e` remains admissible after the belief-first step. -/
theorem gate33_e_after_belP_admissible :
    ConditionalizationAdmissible Gate33BelFirst dynamicInstabilityEvidence := by
  constructor
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel

/-- Final posterior for the order `B p ; e`. -/
def Gate33BelThenE :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate33BelFirst dynamicInstabilityEvidence
    gate33_e_after_belP_admissible

/-- Atomic-first posterior is the already verified instability update. -/
def Gate33EFirst :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  DynamicInstabilityUpdated

/-- After `e`, `B p` has positive extension `{a,c}` and still has nonzero local
mass at every source world, so the second update is admissible. -/
theorem gate33_belP_after_e_admissible :
    ConditionalizationAdmissible Gate33EFirst gate33BelPEvidence := by
  constructor
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel

/-- Final posterior for the order `e ; B p`. -/
def Gate33EThenBel :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate33EFirst gate33BelPEvidence
    gate33_belP_after_e_admissible

/-- Before any update the positive extension of belief evidence is the entire
accessible three-world state space. -/
theorem gate33_belP_event_initial_full :
    conditionalizationEvidenceEvent DynamicInstabilityModel
      DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence =
      [DynamicInstabilityWorld.a,
       DynamicInstabilityWorld.b,
       DynamicInstabilityWorld.c] := by
  decide +kernel

/-- After learning `e`, the same syntactic belief evidence has changed its
positive extension: world `b` is no longer positive for `B p`. -/
theorem gate33_belP_event_after_e_shrinks :
    conditionalizationEvidenceEvent Gate33EFirst
      DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence =
      [DynamicInstabilityWorld.a, DynamicInstabilityWorld.c] := by
  decide +kernel

/-- The evidence formula is therefore genuinely update-sensitive. -/
theorem gate33_belP_evidence_extension_changes :
    conditionalizationEvidenceEvent DynamicInstabilityModel
        DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence ≠
      conditionalizationEvidenceEvent Gate33EFirst
        DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence := by
  rw [gate33_belP_event_initial_full, gate33_belP_event_after_e_shrinks]
  decide

/-- Processing `B p` before `e` ends in the familiar fractured profile
`T/N/T`. -/
theorem gate33_bel_then_e_profile :
    evalModal Gate33BelThenE DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate33BelThenE DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.N ∧
    evalModal Gate33BelThenE DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- Processing `e` before the now update-sensitive evidence `B p` restores a
homogeneous `T/T/T` belief profile. -/
theorem gate33_e_then_bel_profile :
    evalModal Gate33EThenBel DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate33EThenBel DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate33EThenBel DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- The two orders are not merely represented differently: they disagree on a
modal observation at world `b`. -/
theorem gate33_orders_modally_diverge :
    evalModal Gate33BelThenE DynamicInstabilityWorld.b dynamicInstabilityBelP ≠
      evalModal Gate33EThenBel DynamicInstabilityWorld.b dynamicInstabilityBelP := by
  rw [gate33_bel_then_e_profile.2.1, gate33_e_then_bel_profile.2.1]
  decide

/-- Belief-first then atomic evidence ends outside compositional Recovery. -/
theorem gate33_bel_then_e_not_recovered :
    ¬ ModalFormula.CompositionalRecovery
      Gate33BelThenE dynamicInstabilityBelP := by
  intro hRecovery
  have hIncomplete :
      ¬ BeliefThresholdComplete Gate33BelThenE
        DynamicInstabilityAgent.i DynamicInstabilityWorld.b
        (fun u => evalModal Gate33BelThenE u dynamicInstabilityP) := by
    exact not_beliefThresholdComplete_of_evalModal_bel_eq_N
      Gate33BelThenE DynamicInstabilityAgent.i DynamicInstabilityWorld.b
      dynamicInstabilityP gate33_bel_then_e_profile.2.1
  exact hIncomplete (hRecovery DynamicInstabilityWorld.b).2

/-- Atomic evidence first then belief evidence ends inside compositional
Recovery. -/
theorem gate33_e_then_bel_recovered :
    ModalFormula.CompositionalRecovery
      Gate33EThenBel dynamicInstabilityBelP := by
  intro w
  constructor
  · intro u _
    cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rcases gate33_e_then_bel_profile with ⟨ha, hb, hc⟩
    cases w
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate33EThenBel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityP ha
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate33EThenBel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.b dynamicInstabilityP hb
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate33EThenBel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.c dynamicInstabilityP hc

/-- Concrete Gate-33 hysteresis theorem: the same two syntactic evidence
ingredients `{e, B p}`, in opposite orders, produce opposite Recovery outcomes. -/
theorem gate33_same_evidence_ingredients_different_recovery :
    (¬ ModalFormula.CompositionalRecovery
        Gate33BelThenE dynamicInstabilityBelP) ∧
    ModalFormula.CompositionalRecovery
        Gate33EThenBel dynamicInstabilityBelP := by
  exact ⟨gate33_bel_then_e_not_recovered, gate33_e_then_bel_recovered⟩

/-! ## Static boundary: no atomic Recovery hysteresis -/

/-- Gate 30 excludes Recovery hysteresis for two static atomic evidence events:
under integrity and mutual sequential admissibility, reversing their order
cannot change the Recovery status of any modal formula. -/
theorem gate33_no_two_atom_recovery_hysteresis
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom)
    (hIntegrity : ModelProbabilityIntegrity m)
    (p q : Atom)
    (hP : ConditionalizationAdmissible m (Formula.prop p))
    (hQ : ConditionalizationAdmissible m (Formula.prop q))
    (hQAfterP : ConditionalizationAdmissible
      (conditionalize m (Formula.prop p) hP) (Formula.prop q))
    (hPAfterQ : ConditionalizationAdmissible
      (conditionalize m (Formula.prop q) hQ) (Formula.prop p))
    (phi : ModalFormula Atom Ag) :
    ¬ ((ModalFormula.CompositionalRecovery
          (conditionalize
            (conditionalize m (Formula.prop p) hP)
            (Formula.prop q) hQAfterP) phi ∧
        ¬ ModalFormula.CompositionalRecovery
          (conditionalize
            (conditionalize m (Formula.prop q) hQ)
            (Formula.prop p) hPAfterQ) phi) ∨
      (ModalFormula.CompositionalRecovery
          (conditionalize
            (conditionalize m (Formula.prop q) hQ)
            (Formula.prop p) hPAfterQ) phi ∧
        ¬ ModalFormula.CompositionalRecovery
          (conditionalize
            (conditionalize m (Formula.prop p) hP)
            (Formula.prop q) hQAfterP) phi)) := by
  have hConfluent := conditionalize_two_atoms_recovery_confluent
    m hIntegrity p q hP hQ hQAfterP hPAfterQ phi
  intro hHysteresis
  rcases hHysteresis with hPQ | hQP
  · exact hPQ.2 (hConfluent.mp hPQ.1)
  · exact hQP.2 (hConfluent.mpr hQP.1)

/-!
## Gate-33 boundary

The verified phenomenon is **endogenous-evidence hysteresis**:

```text
same syntactic ingredients: {e, B p}
order 1: B p ; e  -> T/N/T -> Non-Recovery
order 2: e ; B p  -> T/T/T -> Recovery
```

The mechanism is not mysterious numerical noncommutativity. Atomic Bayes
conditioning remains confluent in the Gate-30 regime. History enters because
the first update changes what the later belief-dependent evidence formula
positively denotes.

Accordingly Gate 33 should not be paraphrased as "fixed evidence sets fail to
commute". The stronger and more accurate diagnosis is:

**when evidence content is evaluated inside the evolving epistemic model, the
same syntactic information schedule can acquire history-dependent extensional
content, and that semantic feedback can change the eventual Recovery phase.**
-/

end PEL4
