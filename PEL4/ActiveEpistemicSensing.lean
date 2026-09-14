import PEL4.NoisyValueOfInformation

namespace PEL4

/-!
# Gate 64: active epistemic sensing

Gate 63 established that a noisy signal can have positive decision value because
later responses may depend on it. Gate 64 makes sensing itself a controlled
choice. The agent chooses between a cheaper weaker sensor and a costlier more
accurate sensor, then compares net expected downstream value.
-/

inductive Gate64Sensor where
  | cheap
  | precise
  deriving DecidableEq, Repr

/-- Exact finite likelihood of a sensing signal. The cheap sensor is 75/25;
the precise sensor is 90/10. Both classify hidden states through Gate 55's
coarse Recovery observation, while differing in reliability. -/
def gate64SensorLikelihood
    (sensor : Gate64Sensor)
    (state : Gate47State)
    (observation : Gate55Observation) : Rat :=
  match sensor with
  | .cheap =>
      if gate55Observe state = observation then (3 : Rat) / 4 else (1 : Rat) / 4
  | .precise =>
      if gate55Observe state = observation then (9 : Rat) / 10 else (1 : Rat) / 10

/-- Multiply the current hidden-state belief by one sensor likelihood. -/
def gate64SensorObservationWeight
    (sensor : Gate64Sensor)
    (observation : Gate55Observation)
    (belief : BayesianEpistemicBelief Gate47State) :
    BayesianEpistemicBelief Gate47State :=
  belief.map fun item =>
    (item.1 * gate64SensorLikelihood sensor item.2 observation, item.2)

/-- Marginal probability of a signal under a chosen sensor. -/
def gate64SensorObservationProbability
    (sensor : Gate64Sensor)
    (belief : BayesianEpistemicBelief Gate47State)
    (observation : Gate55Observation) : Rat :=
  bayesianBeliefMassSum <|
    gate64SensorObservationWeight sensor observation belief

/-- Bayesian posterior after choosing a sensor and observing its signal. -/
def gate64SensorPosterior
    (sensor : Gate64Sensor)
    (belief : BayesianEpistemicBelief Gate47State)
    (observation : Gate55Observation) :
    BayesianEpistemicBelief Gate47State :=
  normalizeBayesianBeliefGeneric <|
    gate64SensorObservationWeight sensor observation belief

/-- Cost of using a sensor in the finite witness. -/
def gate64SensorCost : Gate64Sensor -> Rat
  | .cheap => 0
  | .precise => (1 : Rat) / 2

/-- Observation-contingent response used after sensing. Recovery triggers hold;
Non-Recovery triggers repair. -/
def gate64ResponseForObservation : Gate55Observation -> Gate63Response
  | .recovery => .hold
  | .nonRecovery => .repair

/-- Gross expected downstream response value of a sensor. -/
def gate64SensorGrossValue (sensor : Gate64Sensor) : Rat :=
  ([Gate55Observation.recovery, Gate55Observation.nonRecovery].map fun obs =>
    gate64SensorObservationProbability sensor gate63PredictedBelief obs *
      gate63ResponseValue
        (gate64SensorPosterior sensor gate63PredictedBelief obs)
        (gate64ResponseForObservation obs)).sum

/-- Net sensing value after subtracting sensor cost. -/
def gate64SensorNetValue (sensor : Gate64Sensor) : Rat :=
  gate64SensorGrossValue sensor - gate64SensorCost sensor

/-- Cheap Recovery signal gives a 3/4 robust posterior. -/
theorem gate64_cheap_recovery_posterior :
    gate64SensorPosterior .cheap gate63PredictedBelief .recovery =
      [((1 : Rat) / 4, .destabilized), ((3 : Rat) / 4, .robust)] := by
  native_decide

/-- Cheap Non-Recovery signal reverses the 3/4 and 1/4 weights. -/
theorem gate64_cheap_nonRecovery_posterior :
    gate64SensorPosterior .cheap gate63PredictedBelief .nonRecovery =
      [((3 : Rat) / 4, .destabilized), ((1 : Rat) / 4, .robust)] := by
  native_decide

/-- Each cheap-sensor signal has probability one half in the symmetric prior. -/
theorem gate64_cheap_signal_probabilities :
    gate64SensorObservationProbability .cheap gate63PredictedBelief .recovery =
        (1 : Rat) / 2 ∧
    gate64SensorObservationProbability .cheap gate63PredictedBelief .nonRecovery =
        (1 : Rat) / 2 := by
  constructor <;> native_decide

/-- The cheap sensor has gross and net value 29/4 because its cost is zero. -/
theorem gate64_cheap_net_value :
    gate64SensorNetValue .cheap = (29 : Rat) / 4 := by
  native_decide

/-- The precise sensor reproduces the Gate-63 90/10 signal quality, giving gross
value 83/10 and net value 39/5 after its one-half sensing cost. -/
theorem gate64_precise_gross_value :
    gate64SensorGrossValue .precise = (83 : Rat) / 10 := by
  native_decide

theorem gate64_precise_net_value :
    gate64SensorNetValue .precise = (39 : Rat) / 5 := by
  native_decide

/-- In this explicit menu, the more accurate sensor remains worth buying after
its cost: 39/5 exceeds 29/4 by 11/20. -/
theorem gate64_precise_sensor_strictly_preferred :
    gate64SensorNetValue .precise > gate64SensorNetValue .cheap := by
  native_decide

theorem gate64_sensor_advantage :
    gate64SensorNetValue .precise - gate64SensorNetValue .cheap =
      (11 : Rat) / 20 := by
  native_decide

/-- Main Gate-64 result: active epistemic sensing selects the costlier precise
test in this finite witness because its extra downstream decision value exceeds
its sensing cost. -/
theorem gate64_active_epistemic_sensing_selects_precise_test :
    gate64SensorNetValue .cheap = (29 : Rat) / 4 ∧
    gate64SensorNetValue .precise = (39 : Rat) / 5 ∧
    gate64SensorNetValue .precise > gate64SensorNetValue .cheap ∧
    gate64SensorNetValue .precise - gate64SensorNetValue .cheap =
      (11 : Rat) / 20 := by
  exact ⟨gate64_cheap_net_value,
    gate64_precise_net_value,
    gate64_precise_sensor_strictly_preferred,
    gate64_sensor_advantage⟩

/-!
## Gate-64 boundary

The preference is relative to this specified prior, sensor menu, downstream
response payoffs, and costs. It does not prove that more precise sensors are
always optimal or that epistemic agents should always pay for information. It
proves that sensing can itself be an optimized action once informational value
and acquisition cost are represented together.
-/

end PEL4
