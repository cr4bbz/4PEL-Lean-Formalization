import PEL4.EpistemicIdentifiability

namespace PEL4

/-!
# Gate 66: repeated evidence and posterior learning

Gate 65 separated hidden-state pairs that are identifiable by the current sensor
family from pairs that are structurally aliased by it. Gate 66 asks what repeated
sampling can and cannot accomplish.

For the identifiable pair `.robust` / `.destabilized`, repeated precise Recovery
signals progressively concentrate posterior mass on `.robust`. For the aliased
pair `.fragile` / `.robust`, every Gate-64 sensor assigns identical likelihoods,
so repeated observations of any fixed sensor/outcome leave the symmetric prior
exactly unchanged for arbitrarily many repetitions.
-/

/-- Repeatedly condition a hidden-state belief on the same chosen sensor and
observed signal. -/
def gate66RepeatedSensorPosterior
    (sensor : Gate64Sensor)
    (observation : Gate55Observation) :
    Nat -> BayesianEpistemicBelief Gate47State ->
      BayesianEpistemicBelief Gate47State
  | 0, belief => belief
  | n + 1, belief =>
      gate64SensorPosterior sensor
        (gate66RepeatedSensorPosterior sensor observation n belief)
        observation

/-- Symmetric prior over the two states that Gate 65 proved observationally
aliased under the entire Gate-64 sensor family. -/
def gate66AliasedPrior : BayesianEpistemicBelief Gate47State :=
  [((1 : Rat) / 2, .fragile), ((1 : Rat) / 2, .robust)]

/-- Posterior mass on the robust state after repeatedly seeing the precise
sensor's Recovery signal from the identifiable Gate-63 predicted belief. -/
def gate66RobustMassAfterPreciseRecovery (n : Nat) : Rat :=
  bayesianWeightAt
    (gate66RepeatedSensorPosterior .precise .recovery n gate63PredictedBelief)
    .robust

/-- Before new evidence, robust and destabilized each have mass one half. -/
theorem gate66_identifiable_mass_at_zero :
    gate66RobustMassAfterPreciseRecovery 0 = (1 : Rat) / 2 := by
  native_decide

/-- One precise Recovery signal yields the familiar 9/10 robust posterior. -/
theorem gate66_identifiable_mass_after_one :
    gate66RobustMassAfterPreciseRecovery 1 = (9 : Rat) / 10 := by
  native_decide

/-- Two matching precise signals multiply the likelihood ratio, giving 81/82. -/
theorem gate66_identifiable_mass_after_two :
    gate66RobustMassAfterPreciseRecovery 2 = (81 : Rat) / 82 := by
  native_decide

/-- Three matching precise signals yield 729/730 robust posterior mass. -/
theorem gate66_identifiable_mass_after_three :
    gate66RobustMassAfterPreciseRecovery 3 = (729 : Rat) / 730 := by
  native_decide

/-- The finite witness exhibits strict posterior concentration across the first
three repeated informative measurements. -/
theorem gate66_identifiable_repetition_strictly_concentrates :
    gate66RobustMassAfterPreciseRecovery 0 <
        gate66RobustMassAfterPreciseRecovery 1 ∧
    gate66RobustMassAfterPreciseRecovery 1 <
        gate66RobustMassAfterPreciseRecovery 2 ∧
    gate66RobustMassAfterPreciseRecovery 2 <
        gate66RobustMassAfterPreciseRecovery 3 := by
  native_decide

/-- Any single Gate-64 observation leaves the symmetric fragile/robust prior
unchanged. The two hidden states have identical likelihoods, so Bayes has no
basis for changing their relative odds. -/
theorem gate66_aliased_prior_one_step_fixed
    (sensor : Gate64Sensor)
    (observation : Gate55Observation) :
    gate64SensorPosterior sensor gate66AliasedPrior observation =
      gate66AliasedPrior := by
  cases sensor <;> cases observation <;> native_decide

/-- Structural aliasing survives arbitrarily many repetitions of any fixed
Gate-64 sensor/outcome pair. Repetition cannot recover a distinction that the
likelihood model never exposes. -/
theorem gate66_alias_survives_all_repetitions
    (sensor : Gate64Sensor)
    (observation : Gate55Observation)
    (n : Nat) :
    gate66RepeatedSensorPosterior sensor observation n gate66AliasedPrior =
      gate66AliasedPrior := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [gate66RepeatedSensorPosterior, ih,
        gate66_aliased_prior_one_step_fixed]

/-- Consequently, robust posterior mass stays exactly one half forever on the
aliased fragile/robust prior, regardless of which existing sensor/outcome is
repeated. -/
theorem gate66_aliased_robust_mass_stays_half
    (sensor : Gate64Sensor)
    (observation : Gate55Observation)
    (n : Nat) :
    bayesianWeightAt
        (gate66RepeatedSensorPosterior sensor observation n gate66AliasedPrior)
        .robust =
      (1 : Rat) / 2 := by
  rw [gate66_alias_survives_all_repetitions]
  native_decide

/-- Main Gate-66 theorem: repeated evidence separates statistical uncertainty
from structural non-identifiability. Informative repeated measurements sharpen
the posterior in the identifiable witness, while structurally aliased states
remain exactly unresolved under arbitrary repetition of the current sensor
family. -/
theorem gate66_repeated_evidence_learning_boundary :
    gate66RobustMassAfterPreciseRecovery 0 = (1 : Rat) / 2 ∧
    gate66RobustMassAfterPreciseRecovery 1 = (9 : Rat) / 10 ∧
    gate66RobustMassAfterPreciseRecovery 2 = (81 : Rat) / 82 ∧
    gate66RobustMassAfterPreciseRecovery 3 = (729 : Rat) / 730 ∧
    gate66RobustMassAfterPreciseRecovery 0 <
        gate66RobustMassAfterPreciseRecovery 1 ∧
    gate66RobustMassAfterPreciseRecovery 1 <
        gate66RobustMassAfterPreciseRecovery 2 ∧
    gate66RobustMassAfterPreciseRecovery 2 <
        gate66RobustMassAfterPreciseRecovery 3 ∧
    (∀ sensor observation n,
      gate66RepeatedSensorPosterior sensor observation n gate66AliasedPrior =
        gate66AliasedPrior) := by
  exact ⟨gate66_identifiable_mass_at_zero,
    gate66_identifiable_mass_after_one,
    gate66_identifiable_mass_after_two,
    gate66_identifiable_mass_after_three,
    gate66_identifiable_repetition_strictly_concentrates.1,
    gate66_identifiable_repetition_strictly_concentrates.2.1,
    gate66_identifiable_repetition_strictly_concentrates.2.2,
    gate66_alias_survives_all_repetitions⟩

/-!
## Gate-66 boundary

The increasing sequence is a finite exact witness, not yet a general asymptotic
Bayesian consistency theorem. The no-learning result is stronger within its
scope: for the symmetric fragile/robust prior and the current Gate-64 sensors,
repeating any fixed sensor/outcome leaves the belief exactly unchanged for every
finite repetition count. Gate 67 therefore asks whether the experiment family
itself can be enriched to break that alias.
-/

end PEL4
