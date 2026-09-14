import PEL4.DiscountedBellmanFixedPoint

namespace PEL4

/-!
# Gate 76: four-valued epistemic-control bridge

The preceding control gates optimized posterior utility. Gate 76 reconnects the
controller to 4PEL itself. For the proposition "the hidden state is robust", we
read posterior mass on `.robust` as positive support and posterior mass on
`.fragile` as negative support, each through a threshold of `3/4`.

At the symmetric alias neither side crosses the threshold, so the proposition is
`N`. The Gate-69 optimal stress probe moves the posterior after one observation
to either `T` or `F`, depending on the outcome.
-/

/-- Four-valued status of the robustness proposition under a Bayesian hidden-state
belief. Positive and negative support are thresholded independently. -/
def gate76RobustStatus
    (belief : BayesianEpistemicBelief Gate47State) : FDEValue :=
  { pos := decide ((3 : Rat) / 4 ≤ bayesianWeightAt belief .robust)
    neg := decide ((3 : Rat) / 4 ≤ bayesianWeightAt belief .fragile) }

/-- The unresolved symmetric alias is a genuine information gap at threshold
`3/4`: neither robustness nor fragility has enough posterior support. -/
theorem gate76_alias_is_gap :
    gate76RobustStatus gate66AliasedPrior = FDEValue.N := by
  native_decide

/-- A Recovery report from the optimal stress probe moves the robustness claim
to strict positive support. -/
theorem gate76_stress_recovery_is_true :
    gate76RobustStatus
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior .recovery) =
      FDEValue.T := by
  native_decide

/-- A Non-Recovery report moves the same claim to strict negative support. -/
theorem gate76_stress_nonRecovery_is_false :
    gate76RobustStatus
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior .nonRecovery) =
      FDEValue.F := by
  native_decide

/-- The Gate-69 Bellman controller chooses exactly the experiment that generates
these four-valued transitions. -/
theorem gate76_controller_selects_status_resolving_probe :
    gate69ChooseDecision 1 gate66AliasedPrior = .sample .stressProbe :=
  gate69_policy_samples_stress_at_alias

/-- Both possible observations leave the initial gap. -/
theorem gate76_stress_always_resolves_gap
    (observation : Gate55Observation) :
    gate76RobustStatus
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) ≠
      FDEValue.N := by
  cases observation <;> native_decide

/-- Main Gate-76 theorem: an optimal Bayesian sensing action can be interpreted
as a controlled transition in the four-valued epistemic state space. -/
theorem gate76_four_valued_epistemic_control_bridge :
    gate76RobustStatus gate66AliasedPrior = FDEValue.N ∧
    gate69ChooseDecision 1 gate66AliasedPrior = .sample .stressProbe ∧
    gate76RobustStatus
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior .recovery) =
      FDEValue.T ∧
    gate76RobustStatus
        (gate67ExperimentPosterior .stressProbe gate66AliasedPrior .nonRecovery) =
      FDEValue.F ∧
    (∀ observation,
      gate76RobustStatus
          (gate67ExperimentPosterior .stressProbe gate66AliasedPrior observation) ≠
        FDEValue.N) := by
  exact ⟨gate76_alias_is_gap,
    gate76_controller_selects_status_resolving_probe,
    gate76_stress_recovery_is_true,
    gate76_stress_nonRecovery_is_false,
    gate76_stress_always_resolves_gap⟩

/-!
## Gate-76 boundary

The support interpretation is proposition-specific: `.robust` contributes
positive support and `.fragile` negative support. Gate 76 does not claim that
every hidden-state posterior canonically induces every 4PEL proposition. What it
establishes is the missing bridge principle: a Bellman-optimal information action
can induce a machine-checked `N -> T/F` transition under independent 4PEL support
thresholds.
-/

end PEL4
