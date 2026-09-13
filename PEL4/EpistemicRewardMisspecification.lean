import PEL4.ActiveEvidenceControl

namespace PEL4

/-!
# Gate 46: epistemic reward misspecification and information avoidance

Gate 45 gave an agent active control over which evidence-acquisition plan to
execute. Gate 46 adds the smallest possible reward layer needed to study a
failure mode: a one-step objective that rewards only immediate Recovery can
prefer an information-acquisition action that preserves Recovery over an
available action that destroys it.

The formal result is deliberately local. It does not yet say that the
Recovery-destroying action is truth-conducive, globally informative, or better
in the long run. Those stronger claims require a temporal or truth-directed
objective in a later gate.
-/

/-- A one-step reward used to assess a realized controlled transition. -/
abbrev OneStepEpistemicReward (State Action : Type) :=
  State -> Action -> State -> Nat

/-- Strict one-step preference induced by a reward. -/
def OneStepStrictlyPrefers
    {State Action : Type}
    (reward : OneStepEpistemicReward State Action)
    (start : State)
    (preferred preferredOut alternative alternativeOut : State × Action × State) : Prop :=
  reward start preferred.2.1 preferred.2.2 >
    reward start alternative.2.1 alternative.2.2

/-- A generic local witness that an immediate-status reward prefers one
available controlled branch over another with a different status. -/
structure OneStepStatusAvoidanceWitness
    (State Action : Type)
    (Step : State -> Action -> State -> Prop)
    (Recovered : State -> Prop)
    (reward : OneStepEpistemicReward State Action) where
  start : State
  preferredAction : Action
  alternativeAction : Action
  preferredOut : State
  alternativeOut : State
  preferredStep : Step start preferredAction preferredOut
  alternativeStep : Step start alternativeAction alternativeOut
  preferredRecovered : Recovered preferredOut
  alternativeNotRecovered : ¬ Recovered alternativeOut
  strictRewardPreference :
    reward start preferredAction preferredOut >
      reward start alternativeAction alternativeOut

/-! ## Concrete two-action Gate-46 decision problem -/

/-- Two acquisition choices extracted from Gate 45. -/
inductive Gate46Choice where
  | preserve
  | probe
  deriving DecidableEq, Repr

/-- The Gate-45 acquisition plan selected by each Gate-46 choice. -/
def gate46Plan : Gate46Choice -> Gate45Plan
  | .preserve => gate45SafePlan
  | .probe => gate45DisruptivePlan

/-- The realized successor associated with each deterministic Gate-45 plan. -/
def gate46Outcome : Gate46Choice ->
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom
  | .preserve => Gate29RecoveryPreservingUpdated
  | .probe => DynamicInstabilityUpdated

/-- Controlled transition relation for the binary Gate-46 menu. -/
def Gate46ChoiceStep
    (m : Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom)
    (choice : Gate46Choice)
    (out : Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom) : Prop :=
  ActiveEvidencePlanStep gate45DirectSemantics m (gate46Plan choice) out

/-- Both menu choices have the advertised realized successor. -/
theorem gate46_choice_step (choice : Gate46Choice) :
    Gate46ChoiceStep DynamicInstabilityModel choice (gate46Outcome choice) := by
  cases choice with
  | preserve => exact gate45_safePlan_step
  | probe => exact gate45_disruptivePlan_step

/-- Recovery predicate used by the Gate-46 reward witness. -/
def Gate46Recovered
    (m : Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom) : Prop :=
  ModalFormula.CompositionalRecovery m dynamicInstabilityBelP

/-- Naive immediate Recovery reward on the two-action menu.

The score is intentionally only a proxy specification for this concrete menu:
`preserve` receives one point and `probe` zero. The calibration theorem below
shows that, on the realized Gate-45 successors, this exactly tracks immediate
Recovery versus Non-Recovery. -/
def gate46ImmediateRecoveryReward :
    OneStepEpistemicReward
      (Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom)
      Gate46Choice :=
  fun _ choice _ =>
    match choice with
    | .preserve => 1
    | .probe => 0

/-- The naive reward is correctly calibrated to immediate Recovery on the
concrete two-choice witness. -/
theorem gate46_reward_calibrated_on_realized_outcomes :
    gate46ImmediateRecoveryReward DynamicInstabilityModel .preserve
        (gate46Outcome .preserve) = 1 ∧
    Gate46Recovered (gate46Outcome .preserve) ∧
    gate46ImmediateRecoveryReward DynamicInstabilityModel .probe
        (gate46Outcome .probe) = 0 ∧
    ¬ Gate46Recovered (gate46Outcome .probe) := by
  exact ⟨rfl,
    gate29_recoveryPreserving_update_recovered,
    rfl,
    dynamic_instability_belP_not_recovered_after⟩

/-- The two actively selectable acquisition choices genuinely lead to distinct
full epistemic states. -/
theorem gate46_realized_outcomes_distinct :
    gate46Outcome .preserve ≠ gate46Outcome .probe := by
  intro hEq
  have hRecovered : Gate46Recovered (gate46Outcome .preserve) :=
    gate29_recoveryPreserving_update_recovered
  rw [hEq] at hRecovered
  exact dynamic_instability_belP_not_recovered_after hRecovered

/-- A choice is myopically optimal when its immediate reward is at least as
large as the reward of every choice in the binary acquisition menu. -/
def Gate46MyopicallyOptimal (choice : Gate46Choice) : Prop :=
  ∀ alternative : Gate46Choice,
    gate46ImmediateRecoveryReward DynamicInstabilityModel choice
        (gate46Outcome choice) ≥
      gate46ImmediateRecoveryReward DynamicInstabilityModel alternative
        (gate46Outcome alternative)

/-- Preserving immediate Recovery is myopically optimal. -/
theorem gate46_preserve_is_myopically_optimal :
    Gate46MyopicallyOptimal .preserve := by
  intro alternative
  cases alternative <;> decide

/-- The disruptive probe is not myopically optimal under the naive reward. -/
theorem gate46_probe_not_myopically_optimal :
    ¬ Gate46MyopicallyOptimal .probe := by
  intro hOptimal
  have h := hOptimal .preserve
  norm_num at h

/-- The naive one-step objective has a unique optimum: every myopically optimal
choice must be the Recovery-preserving acquisition plan. -/
theorem gate46_unique_myopic_optimum
    (choice : Gate46Choice)
    (hOptimal : Gate46MyopicallyOptimal choice) :
    choice = .preserve := by
  cases choice with
  | preserve => rfl
  | probe => exact False.elim (gate46_probe_not_myopically_optimal hOptimal)

/-- Main Gate-46 information-avoidance witness. Both actions are realized
controlled steps from the same epistemic state, but the immediate-Recovery
reward strictly prefers the branch that preserves Recovery and rejects the
branch that disrupts it. -/
def gate46_information_avoidance_witness :
    OneStepStatusAvoidanceWitness
      (Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom)
      Gate46Choice
      Gate46ChoiceStep
      Gate46Recovered
      gate46ImmediateRecoveryReward where
  start := DynamicInstabilityModel
  preferredAction := .preserve
  alternativeAction := .probe
  preferredOut := gate46Outcome .preserve
  alternativeOut := gate46Outcome .probe
  preferredStep := gate46_choice_step .preserve
  alternativeStep := gate46_choice_step .probe
  preferredRecovered := gate29_recoveryPreserving_update_recovered
  alternativeNotRecovered := dynamic_instability_belP_not_recovered_after
  strictRewardPreference := by decide

/-- Explicit theorem form of the Gate-46 conclusion. -/
theorem gate46_naive_recovery_reward_selects_information_avoidance :
    Gate46ChoiceStep DynamicInstabilityModel .preserve
        (gate46Outcome .preserve) ∧
    Gate46ChoiceStep DynamicInstabilityModel .probe
        (gate46Outcome .probe) ∧
    Gate46Recovered (gate46Outcome .preserve) ∧
    ¬ Gate46Recovered (gate46Outcome .probe) ∧
    gate46ImmediateRecoveryReward DynamicInstabilityModel .preserve
        (gate46Outcome .preserve) >
      gate46ImmediateRecoveryReward DynamicInstabilityModel .probe
        (gate46Outcome .probe) ∧
    (∀ choice, Gate46MyopicallyOptimal choice -> choice = .preserve) := by
  exact ⟨gate46_choice_step .preserve,
    gate46_choice_step .probe,
    gate29_recoveryPreserving_update_recovered,
    dynamic_instability_belP_not_recovered_after,
    by decide,
    gate46_unique_myopic_optimum⟩

/-!
## Gate-46 boundary

Gate 46 proves a reward-design failure mode only relative to *immediate
Recovery*. The formal witness does not yet establish that the rejected probe is
more truthful, more informative in an information-theoretic sense, or better
under a long-run objective. Accordingly, `reward misspecification` here means
that the reward is deliberately narrow relative to the broader epistemic goals
we intend to study, not that Lean has already proved an external truth standard
that the reward violates.

The next gate should add a temporal objective or delayed Recovery benefit and
ask whether temporary Non-Recovery can be rationally optimal over a longer
horizon.
-/

end PEL4
