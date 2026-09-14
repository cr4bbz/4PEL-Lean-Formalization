# Gates 78-85: Epistemic Self-Trust

This research block extends active epistemic control from uncertainty about the
world to uncertainty about the agent's own evidence channels.

| Gate | Module | Verified witness |
| --- | --- | --- |
| 78 | `ModelUncertaintyWitness` | Sensor-model uncertainty can reverse a probe ranking. |
| 79 | `RobustMaximinControl` | Maximin control can reverse the nominal action. |
| 80 | `CalibrationStatusWitness` | Calibration can move apparent `T` to `N`. |
| 81 | `ValueOfCalibration` | Learning sensor reliability can have positive net value. |
| 82 | `MissingEvidenceAbstention` | Missing evidence is not negative evidence; abstention can dominate coercion. |
| 83 | `AdversarialSensorRobustness` | A hardened lower-ceiling sensor can dominate in worst-case value. |
| 84 | `SensorModelIdentifiability` | Two individually non-identifying diagnostics can jointly identify the sensor model. |
| 85 | `EpistemicSelfDoubtBridge` | Second-order defeat admits the path `T -> N -> (T or F)`. |

## Interpretation

Gates 70-77 made four-valued epistemic states controllable. Gates 78-85 make the
controller itself fallible. The agent can now distinguish first-order uncertainty
about the world from second-order uncertainty about the machinery producing its
evidence. Confidence is therefore not required to increase monotonically with
learning: better meta-evidence may rationally lower a status before calibration
restores a strict conclusion.

## Boundary

All results are finite executable witnesses. They do not yet provide a general
probability distribution over sensor models, a minimax-regret theorem, Bayesian
model selection, or a noisy asymptotic calibration theorem. Those are natural
follow-up gates rather than hidden assumptions of this block.
