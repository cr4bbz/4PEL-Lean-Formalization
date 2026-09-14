import PEL4.AliasBreakingExperimentDesign

namespace PEL4

/-!
# Gate 68: adaptive experiment design and stopping

Gate 67 showed that the fragile/robust alias is broken only when the experiment
class is enriched by a stress probe. Gate 68 makes experiment selection depend
on the current Bayesian belief rather than declaring the stress probe externally.

The finite controller uses one-step expected identification confidence as its
experiment-design objective. Confidence is the larger posterior mass assigned to
the two hidden states of interest, `.fragile` and `.robust`. The agent samples
while this confidence is below a declared threshold and stops once the threshold
is reached.

This is an exact finite witness of adaptive experiment design. It is not yet a
general optimal-design theorem, an entropy criterion, or a multistep Bayesian
experimental-design result.
-/

/-- Identification confidence for the fragile/robust distinction. -/
def gate68IdentificationConfidence
    (belief : BayesianEpistemicBelief Gate47State) : Rat :=
  max (bayesianWeightAt belief .fragile) (bayesianWeightAt belief .robust)

/-- One-step expected confidence after running an experiment. -/
def gate68ExpectedIdentificationConfidence
    (experiment : Gate67Experiment)
    (belief : BayesianEpistemicBelief Gate47State) : Rat :=
  ([Gate55Observation.recovery, Gate55Observation.nonRecovery].map fun observation =>
    gate67ExperimentObservationProbability experiment belief observation *
      gate68IdentificationConfidence
        (gate67ExperimentPosterior experiment belief observation)).sum

/-- Finite argmax over the Gate-67 experiment menu. Ties are deliberately broken
in favor of the stress probe, then the precise status sensor. -/
def gate68ChooseExperiment
    (belief : BayesianEpistemicBelief Gate47State) : Gate67Experiment :=
  let cheap := gate68ExpectedIdentificationConfidence .statusCheap belief
  let precise := gate68ExpectedIdentificationConfidence .statusPrecise belief
  let stress := gate68ExpectedIdentificationConfidence .stressProbe belief
  if stress ≥ precise ∧ stress ≥ cheap then
    .stressProbe
  else if precise ≥ cheap then
    .statusPrecise
  else
    .statusCheap

/-- Declared stopping threshold for the finite identification witness. -/
def gate68IdentificationThreshold : Rat := (9 : Rat) / 10

/-- The controller either stops or samples one selected experiment. -/
inductive Gate68Decision where
  | stop
  | sample (experiment : Gate67Experiment)
  deriving DecidableEq, Repr

/-- Posterior-dependent experiment policy with threshold stopping. -/
def gate68AdaptivePolicy
    (belief : BayesianEpistemicBelief Gate47State) : Gate68Decision :=
  if gate68IdentificationThreshold ≤ gate68IdentificationConfidence belief then
    .stop
  else
    .sample (gate68ChooseExperiment belief)

/-- The symmetric aliased prior has confidence exactly one half. -/
theorem gate68_alias_prior_confidence :
    gate68IdentificationConfidence gate66AliasedPrior = (1 : Rat) / 2 := by
  native_decide

/-- Repeating either old status experiment has no one-step identification gain
on the aliased prior. -/
theorem gate68_old_experiments_expected_confidence :
    gate68ExpectedIdentificationConfidence .statusCheap gate66AliasedPrior =
        (1 : Rat) / 2 ∧
    gate68ExpectedIdentificationConfidence .statusPrecise gate66AliasedPrior =
        (1 : Rat) / 2 := by
  constructor <;> native_decide

/-- The alias-breaking stress experiment raises expected one-step confidence to
nine tenths. -/
theorem gate68_stress_expected_confidence :
    gate68ExpectedIdentificationConfidence .stressProbe gate66AliasedPrior =
      (9 : Rat) / 10 := by
  native_decide

/-- The stress probe strictly dominates both old status experiments under the
Gate-68 one-step identification objective. -/
theorem gate68_stress_strictly_best_at_alias :
    gate68ExpectedIdentificationConfidence .stressProbe gate66AliasedPrior >
        gate68ExpectedIdentificationConfidence .statusCheap gate66AliasedPrior ∧
    gate68ExpectedIdentificationConfidence .stressProbe gate66AliasedPrior >
        gate68ExpectedIdentificationConfidence .statusPrecise gate66AliasedPrior := by
  constructor <;> native_decide

/-- The finite argmax therefore selects the stress probe from the unresolved
aliased prior. -/
theorem gate68_selector_chooses_stress_probe :
    gate68ChooseExperiment gate66AliasedPrior = .stressProbe := by
  native_decide

/-- The prior is below the stopping threshold, so the adaptive policy samples
rather than stopping. -/
theorem gate68_policy_samples_when_unresolved :
    gate68AdaptivePolicy gate66AliasedPrior = .sample .stressProbe := by
  native_decide

/-- Either possible stress-probe observation produces posterior confidence
exactly at the declared nine-tenths stopping threshold. -/
theorem gate68_stress_observation_reaches_threshold
    (observation : Gate55Observation) :
    gate68IdentificationConfidence
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      gate68IdentificationThreshold := by
  cases observation <;> native_decide

/-- Hence the adaptive policy stops after either possible stress-probe outcome. -/
theorem gate68_policy_stops_after_stress_observation
    (observation : Gate55Observation) :
    gate68AdaptivePolicy
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      .stop := by
  cases observation <;> native_decide

/-- By contrast, one more precise status report leaves the structural alias
unresolved and the adaptive policy still chooses the stress probe. -/
theorem gate68_old_status_evidence_keeps_sampling :
    gate68AdaptivePolicy
        (gate67ExperimentPosterior .statusPrecise gate66AliasedPrior .recovery) =
      .sample .stressProbe := by
  native_decide

/-- Main Gate-68 theorem: experiment selection is belief-dependent, the current
alias makes the stress probe uniquely better under the declared one-step
confidence objective, and either stress outcome crosses the stopping threshold.
More data from the old measurement dimension does not trigger stopping. -/
theorem gate68_adaptive_experiment_design_and_stopping :
    gate68IdentificationConfidence gate66AliasedPrior = (1 : Rat) / 2 ∧
    gate68ExpectedIdentificationConfidence .statusCheap gate66AliasedPrior =
        (1 : Rat) / 2 ∧
    gate68ExpectedIdentificationConfidence .statusPrecise gate66AliasedPrior =
        (1 : Rat) / 2 ∧
    gate68ExpectedIdentificationConfidence .stressProbe gate66AliasedPrior =
        (9 : Rat) / 10 ∧
    gate68ChooseExperiment gate66AliasedPrior = .stressProbe ∧
    gate68AdaptivePolicy gate66AliasedPrior = .sample .stressProbe ∧
    (∀ observation,
      gate68AdaptivePolicy
          (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
        .stop) ∧
    gate68AdaptivePolicy
        (gate67ExperimentPosterior .statusPrecise gate66AliasedPrior .recovery) =
      .sample .stressProbe := by
  exact ⟨gate68_alias_prior_confidence,
    gate68_old_experiments_expected_confidence.1,
    gate68_old_experiments_expected_confidence.2,
    gate68_stress_expected_confidence,
    gate68_selector_chooses_stress_probe,
    gate68_policy_samples_when_unresolved,
    gate68_policy_stops_after_stress_observation,
    gate68_old_status_evidence_keeps_sampling⟩

/-!
## Gate-68 boundary

The experiment menu, likelihoods, confidence functional, and 9/10 threshold are
all declared parts of the finite witness. Gate 68 proves that an adaptive policy
can derive the alias-breaking intervention from its current posterior and stop
when the declared identification target is reached. It does not prove that
maximum posterior mass is the uniquely correct uncertainty measure, that this
myopic selector is globally optimal over arbitrary horizons, or that the stress
probe is supplied by physical 4PEL semantics.

A natural Gate 69 is sequential Bayesian experiment design with explicit sensing
cost: compare the expected value of another sample against stopping, so the
stopping rule itself becomes an optimization result rather than a fixed
threshold.
-/

end PEL4
