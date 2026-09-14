import PEL4.RepeatedEvidenceLearning

namespace PEL4

/-!
# Gate 67: alias-breaking experiment design

Gate 66 proved that repetition is powerless against structural aliasing in the
current sensor family. Gate 67 therefore changes the intervention rather than
merely collecting more of the same data.

The expanded experiment menu retains the two status sensors from Gate 64 and
adds a stress probe. The old sensors measure only the coarse Recovery bit, while
the stress probe is declared to expose the hidden robustness distinction: the
verified `.robust` state tends to report Recovery and `.fragile` tends to report
Non-Recovery. This is an experiment-design witness, not a claim that such a
physical probe is already supplied by 4PEL semantics.
-/

inductive Gate67Experiment where
  | statusCheap
  | statusPrecise
  | stressProbe
  deriving DecidableEq, Repr

/-- Likelihood model for the expanded experiment family. The first two
experiments are exactly the Gate-64 status sensors. The stress probe measures a
new hidden feature rather than increasing precision about the old coarse bit. -/
def gate67ExperimentLikelihood
    (experiment : Gate67Experiment)
    (state : Gate47State)
    (observation : Gate55Observation) : Rat :=
  match experiment with
  | .statusCheap => gate64SensorLikelihood .cheap state observation
  | .statusPrecise => gate64SensorLikelihood .precise state observation
  | .stressProbe =>
      let expected : Gate55Observation :=
        match state with
        | .robust => .recovery
        | _ => .nonRecovery
      if expected = observation then (9 : Rat) / 10 else (1 : Rat) / 10

/-- One experiment separates two hidden states when some possible outcome has
different likelihood under those states. -/
def Gate67ExperimentSeparates
    (experiment : Gate67Experiment)
    (left right : Gate47State) : Prop :=
  ∃ observation,
    gate67ExperimentLikelihood experiment left observation ≠
      gate67ExperimentLikelihood experiment right observation

/-- Identifiability relative to the expanded Gate-67 experiment menu. -/
def Gate67ExpandedIdentifiable (left right : Gate47State) : Prop :=
  ∃ experiment, Gate67ExperimentSeparates experiment left right

/-- The old cheap status sensor still cannot separate fragile from robust. -/
theorem gate67_statusCheap_does_not_break_alias :
    ¬ Gate67ExperimentSeparates .statusCheap .fragile .robust := by
  intro h
  rcases h with ⟨observation, hNe⟩
  cases observation <;> native_decide

/-- Nor can the more precise status sensor. Precision about the same coarse
observable does not add a new identifying dimension. -/
theorem gate67_statusPrecise_does_not_break_alias :
    ¬ Gate67ExperimentSeparates .statusPrecise .fragile .robust := by
  intro h
  rcases h with ⟨observation, hNe⟩
  cases observation <;> native_decide

/-- The new stress probe separates fragile from robust: a Recovery outcome has
likelihood 1/10 under fragile and 9/10 under robust. -/
theorem gate67_stress_probe_breaks_alias :
    Gate67ExperimentSeparates .stressProbe .fragile .robust := by
  refine ⟨.recovery, ?_⟩
  native_decide

theorem gate67_stress_probe_recovery_likelihoods :
    gate67ExperimentLikelihood .stressProbe .fragile .recovery =
        (1 : Rat) / 10 ∧
    gate67ExperimentLikelihood .stressProbe .robust .recovery =
        (9 : Rat) / 10 := by
  constructor <;> native_decide

/-- Within this explicit three-experiment menu, the stress probe is the unique
experiment that breaks the fragile/robust alias. -/
theorem gate67_unique_alias_breaker
    (experiment : Gate67Experiment) :
    Gate67ExperimentSeparates experiment .fragile .robust ↔
      experiment = .stressProbe := by
  cases experiment with
  | statusCheap =>
      constructor
      · intro h
        exact False.elim (gate67_statusCheap_does_not_break_alias h)
      · intro h
        cases h
  | statusPrecise =>
      constructor
      · intro h
        exact False.elim (gate67_statusPrecise_does_not_break_alias h)
      · intro h
        cases h
  | stressProbe =>
      constructor
      · intro _
        rfl
      · intro _
        exact gate67_stress_probe_breaks_alias

/-- Therefore the previously aliased pair becomes identifiable once the
experiment class is enriched by the stress probe. -/
theorem gate67_fragile_robust_identifiable_after_expansion :
    Gate67ExpandedIdentifiable .fragile .robust := by
  exact ⟨.stressProbe, gate67_stress_probe_breaks_alias⟩

/-- Unnormalized Bayesian weighting for a chosen Gate-67 experiment. -/
def gate67ExperimentObservationWeight
    (experiment : Gate67Experiment)
    (observation : Gate55Observation)
    (belief : BayesianEpistemicBelief Gate47State) :
    BayesianEpistemicBelief Gate47State :=
  belief.map fun item =>
    (item.1 * gate67ExperimentLikelihood experiment item.2 observation, item.2)

/-- Posterior after a Gate-67 experiment and outcome. -/
def gate67ExperimentPosterior
    (experiment : Gate67Experiment)
    (belief : BayesianEpistemicBelief Gate47State)
    (observation : Gate55Observation) :
    BayesianEpistemicBelief Gate47State :=
  normalizeBayesianBeliefGeneric <|
    gate67ExperimentObservationWeight experiment observation belief

/-- Marginal probability of an experiment outcome. -/
def gate67ExperimentObservationProbability
    (experiment : Gate67Experiment)
    (belief : BayesianEpistemicBelief Gate47State)
    (observation : Gate55Observation) : Rat :=
  bayesianBeliefMassSum <|
    gate67ExperimentObservationWeight experiment observation belief

/-- The old precise status sensor leaves the aliased prior unresolved after a
Recovery report. -/
theorem gate67_old_precise_sensor_still_half_half :
    gate67ExperimentPosterior .statusPrecise gate66AliasedPrior .recovery =
      gate66AliasedPrior := by
  native_decide

/-- A Recovery report from the stress probe changes the same prior to 1/10
fragile and 9/10 robust. -/
theorem gate67_stress_recovery_posterior :
    gate67ExperimentPosterior .stressProbe gate66AliasedPrior .recovery =
      [((1 : Rat) / 10, .fragile), ((9 : Rat) / 10, .robust)] := by
  native_decide

/-- A Non-Recovery stress report reverses the posterior. -/
theorem gate67_stress_nonRecovery_posterior :
    gate67ExperimentPosterior .stressProbe gate66AliasedPrior .nonRecovery =
      [((9 : Rat) / 10, .fragile), ((1 : Rat) / 10, .robust)] := by
  native_decide

/-- Under the symmetric prior both stress outcomes have probability one half. -/
theorem gate67_stress_signal_probabilities :
    gate67ExperimentObservationProbability .stressProbe
        gate66AliasedPrior .recovery = (1 : Rat) / 2 ∧
    gate67ExperimentObservationProbability .stressProbe
        gate66AliasedPrior .nonRecovery = (1 : Rat) / 2 := by
  constructor <;> native_decide

/-- The active alias-breaking choice is the stress probe. -/
def gate67AliasBreakingChoice : Gate67Experiment := .stressProbe

/-- The declared choice is not merely sufficient but unique in the available
menu for the fragile/robust identification objective. -/
theorem gate67_alias_breaking_choice_unique :
    Gate67ExperimentSeparates gate67AliasBreakingChoice .fragile .robust ∧
    ∀ experiment,
      Gate67ExperimentSeparates experiment .fragile .robust ->
        experiment = gate67AliasBreakingChoice := by
  constructor
  · exact gate67_stress_probe_breaks_alias
  · intro experiment h
    exact (gate67_unique_alias_breaker experiment).mp h

/-- Main Gate-67 result: arbitrarily repeating the old sensor family cannot
resolve the alias, but changing the experiment class can. The stress probe is
the unique alias-breaking experiment in the declared menu and immediately moves
the symmetric posterior away from one half. -/
theorem gate67_experiment_design_breaks_structural_alias :
    (∀ sensor observation n,
      gate66RepeatedSensorPosterior sensor observation n gate66AliasedPrior =
        gate66AliasedPrior) ∧
    ¬ Gate67ExperimentSeparates .statusCheap .fragile .robust ∧
    ¬ Gate67ExperimentSeparates .statusPrecise .fragile .robust ∧
    Gate67ExperimentSeparates .stressProbe .fragile .robust ∧
    Gate67ExpandedIdentifiable .fragile .robust ∧
    gate67ExperimentPosterior .stressProbe gate66AliasedPrior .recovery =
      [((1 : Rat) / 10, .fragile), ((9 : Rat) / 10, .robust)] ∧
    (∀ experiment,
      Gate67ExperimentSeparates experiment .fragile .robust ->
        experiment = .stressProbe) := by
  exact ⟨gate66_alias_survives_all_repetitions,
    gate67_statusCheap_does_not_break_alias,
    gate67_statusPrecise_does_not_break_alias,
    gate67_stress_probe_breaks_alias,
    gate67_fragile_robust_identifiable_after_expansion,
    gate67_stress_recovery_posterior,
    fun experiment h => (gate67_unique_alias_breaker experiment).mp h⟩

/-!
## Gate-67 boundary

Gate 67 does not derive a real-world stress test from 4PEL. It declares an
enriched experiment model and proves the consequences of that model. The result
is therefore structural: a hidden distinction that is non-identifiable under one
experiment family can become identifiable when an intervention exposes a new
state-dependent likelihood. The next natural gate is adaptive experiment design:
choose among experiments from the current belief and stop once the identification
objective is sufficiently resolved.
-/

end PEL4
