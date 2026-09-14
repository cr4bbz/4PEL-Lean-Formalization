import PEL4.AdaptiveExperimentDesign

namespace PEL4

/-!
# Gate 69: sequential Bayesian experiment design with sensing cost

Gate 68 chose experiments adaptively but stopped at an externally declared
identification threshold. Gate 69 removes that threshold from the controller.
Stopping is now one action in a finite-horizon Bellman comparison: the agent may
accept its current identification confidence immediately, or pay an explicit
sensing cost and continue from the posterior induced by the observation.

The generic recursion below is deliberately finite. It supports an arbitrary
finite experiment menu and observation menu, but makes no claim yet about
infinite-horizon convergence, entropy-optimal design, or real-world sensing
costs. The concrete witness reuses the Gate-67 experiment family and the Gate-68
identification objective.
-/

/-- Finite sequential experiment-design data. `stopUtility` is the value of
terminating now; `sensingCost` is paid before the next observation. -/
structure FiniteSequentialBayesianExperimentDesign
    (Belief Experiment Observation : Type) where
  experiments : List Experiment
  observations : List Observation
  observationProbability : Experiment -> Belief -> Observation -> Rat
  posterior : Experiment -> Belief -> Observation -> Belief
  stopUtility : Belief -> Rat
  sensingCost : Experiment -> Rat

mutual
  /-- Finite-horizon value with at most `n` further samples available. At every
  positive horizon the controller may stop immediately instead. -/
  def sequentialExperimentValue
      {Belief Experiment Observation : Type}
      (model : FiniteSequentialBayesianExperimentDesign
        Belief Experiment Observation) :
      Nat -> Belief -> Rat
    | 0, belief => model.stopUtility belief
    | n + 1, belief =>
        max (model.stopUtility belief)
          ((model.experiments.map fun experiment =>
            sequentialExperimentQ model n belief experiment).foldl max 0)

  /-- Value of paying for one experiment now and then continuing optimally with
  `remaining` future samples still available. -/
  def sequentialExperimentQ
      {Belief Experiment Observation : Type}
      (model : FiniteSequentialBayesianExperimentDesign
        Belief Experiment Observation)
      (remaining : Nat)
      (belief : Belief)
      (experiment : Experiment) : Rat :=
    - model.sensingCost experiment +
      (model.observations.map fun observation =>
        model.observationProbability experiment belief observation *
          sequentialExperimentValue model remaining
            (model.posterior experiment belief observation)).sum
end

/-- Concrete Gate-69 sensing prices. The stress probe is more expensive than
both status sensors, but its alias-breaking value can still justify the cost. -/
def gate69ExperimentCost : Gate67Experiment -> Rat
  | .statusCheap => (1 : Rat) / 20
  | .statusPrecise => (1 : Rat) / 10
  | .stressProbe => (1 : Rat) / 5

/-- Gate-69 finite sequential design problem. Stopping utility is exactly the
Gate-68 identification confidence, with no independent stopping threshold. -/
def gate69Model :
    FiniteSequentialBayesianExperimentDesign
      (BayesianEpistemicBelief Gate47State)
      Gate67Experiment Gate55Observation where
  experiments := [.statusCheap, .statusPrecise, .stressProbe]
  observations := [.recovery, .nonRecovery]
  observationProbability := gate67ExperimentObservationProbability
  posterior := gate67ExperimentPosterior
  stopUtility := gate68IdentificationConfidence
  sensingCost := gate69ExperimentCost

/-- A Bellman decision is either stopping now or buying one experiment. -/
inductive Gate69Decision where
  | stop
  | sample (experiment : Gate67Experiment)
  deriving DecidableEq, Repr

/-- Finite argmax over stop plus the three available experiments. Ties involving
stopping are deliberately resolved in favor of stopping. -/
def gate69ChooseDecision
    (remaining : Nat)
    (belief : BayesianEpistemicBelief Gate47State) : Gate69Decision :=
  let stop := gate69Model.stopUtility belief
  let cheap := sequentialExperimentQ gate69Model remaining belief .statusCheap
  let precise := sequentialExperimentQ gate69Model remaining belief .statusPrecise
  let stress := sequentialExperimentQ gate69Model remaining belief .stressProbe
  if stop ≥ cheap ∧ stop ≥ precise ∧ stop ≥ stress then
    .stop
  else if stress ≥ precise ∧ stress ≥ cheap then
    .sample .stressProbe
  else if precise ≥ cheap then
    .sample .statusPrecise
  else
    .sample .statusCheap

/-- The unresolved alias is worth one half if the agent stops immediately. -/
theorem gate69_alias_stop_value :
    gate69Model.stopUtility gate66AliasedPrior = (1 : Rat) / 2 := by
  native_decide

/-- With no later sample available, the two old sensors destroy value through
cost alone, while the stress probe has positive net value. -/
theorem gate69_alias_one_sample_q_values :
    sequentialExperimentQ gate69Model 0 gate66AliasedPrior .statusCheap =
        (9 : Rat) / 20 ∧
    sequentialExperimentQ gate69Model 0 gate66AliasedPrior .statusPrecise =
        (2 : Rat) / 5 ∧
    sequentialExperimentQ gate69Model 0 gate66AliasedPrior .stressProbe =
        (7 : Rat) / 10 := by
  constructor
  · native_decide
  · constructor <;> native_decide

/-- The one-sample Bellman value therefore chooses the costly alias-breaking
probe over both stopping and the cheaper but structurally uninformative sensors. -/
theorem gate69_alias_one_sample_value :
    sequentialExperimentValue gate69Model 1 gate66AliasedPrior =
      (7 : Rat) / 10 := by
  native_decide

/-- Even when two samples are available, wasting the first slot on an old status
sensor is strictly worse than probing immediately. The second-step option is
already priced into these Q-values. -/
theorem gate69_alias_two_sample_q_values :
    sequentialExperimentQ gate69Model 1 gate66AliasedPrior .statusCheap =
        (13 : Rat) / 20 ∧
    sequentialExperimentQ gate69Model 1 gate66AliasedPrior .statusPrecise =
        (3 : Rat) / 5 ∧
    sequentialExperimentQ gate69Model 1 gate66AliasedPrior .stressProbe =
        (7 : Rat) / 10 := by
  constructor
  · native_decide
  · constructor <;> native_decide

/-- A second available sampling opportunity does not change the initial optimal
choice: immediate stress probing still yields value seven tenths. -/
theorem gate69_alias_two_sample_value :
    sequentialExperimentValue gate69Model 2 gate66AliasedPrior =
      (7 : Rat) / 10 := by
  native_decide

/-- The endogenous finite-horizon policy therefore samples the stress probe at
the unresolved prior. -/
theorem gate69_policy_samples_stress_at_alias :
    gate69ChooseDecision 1 gate66AliasedPrior = .sample .stressProbe := by
  native_decide

/-- After either stress outcome the stop value is nine tenths. -/
theorem gate69_post_stress_stop_value
    (observation : Gate55Observation) :
    gate69Model.stopUtility
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      (9 : Rat) / 10 := by
  cases observation <;> native_decide

/-- Once the stress probe has resolved the alias to nine-tenths confidence, every
additional one-step sample is worth less than stopping because it must pay a
strictly positive sensing cost. -/
theorem gate69_post_stress_sample_values
    (observation : Gate55Observation) :
    sequentialExperimentQ gate69Model 0
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation)
        .statusCheap = (17 : Rat) / 20 ∧
    sequentialExperimentQ gate69Model 0
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation)
        .statusPrecise = (4 : Rat) / 5 ∧
    sequentialExperimentQ gate69Model 0
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation)
        .stressProbe = (7 : Rat) / 10 := by
  cases observation <;>
    constructor
    · native_decide
    · constructor <;> native_decide

/-- Hence stopping after the informative probe is an optimization result rather
than a threshold rule. -/
theorem gate69_policy_stops_after_stress
    (observation : Gate55Observation) :
    gate69ChooseDecision 0
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      .stop := by
  cases observation <;> native_decide

/-- The same posterior has Bellman value exactly equal to stopping utility. -/
theorem gate69_post_stress_value
    (observation : Gate55Observation) :
    sequentialExperimentValue gate69Model 1
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
      (9 : Rat) / 10 := by
  cases observation <;> native_decide

/-- Buying a cheap status report before the stress probe incurs a strict delay
cost: its two-sample Q-value is thirteen twentieths rather than seven tenths. -/
theorem gate69_cheap_delay_is_strictly_worse :
    sequentialExperimentQ gate69Model 1 gate66AliasedPrior .statusCheap <
      sequentialExperimentQ gate69Model 1 gate66AliasedPrior .stressProbe := by
  native_decide

/-- Main Gate-69 theorem: with explicit sensing prices and Bellman stopping, the
agent rationally buys the expensive alias-breaking experiment while unresolved,
then stops after either outcome. No confidence threshold appears in the policy. -/
theorem gate69_sequential_bayesian_experiment_design_with_cost :
    gate69Model.stopUtility gate66AliasedPrior = (1 : Rat) / 2 ∧
    sequentialExperimentValue gate69Model 2 gate66AliasedPrior =
        (7 : Rat) / 10 ∧
    gate69ChooseDecision 1 gate66AliasedPrior = .sample .stressProbe ∧
    sequentialExperimentQ gate69Model 1 gate66AliasedPrior .statusCheap <
        sequentialExperimentQ gate69Model 1 gate66AliasedPrior .stressProbe ∧
    (∀ observation,
      gate69Model.stopUtility
          (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
        (9 : Rat) / 10) ∧
    (∀ observation,
      gate69ChooseDecision 0
          (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) =
        .stop) := by
  exact ⟨gate69_alias_stop_value,
    gate69_alias_two_sample_value,
    gate69_policy_samples_stress_at_alias,
    gate69_cheap_delay_is_strictly_worse,
    gate69_post_stress_stop_value,
    gate69_policy_stops_after_stress⟩

/-!
## Gate-69 boundary

The stopping rule is now endogenous relative to the declared utility and sensing
costs, but those utilities and costs remain model inputs. The theorem does not
show that `1/20`, `1/10`, and `1/5` are uniquely correct costs, nor that maximum
posterior mass is a uniquely correct epistemic utility. The recursion is finite
horizon and the experiment likelihoods remain fixed and known.

What Gate 69 establishes is narrower and stronger: once sensing has a price,
"stop" can be treated as a genuine epistemic action and can become optimal by
Bellman comparison rather than by an externally imposed confidence cutoff.
-/

end PEL4
