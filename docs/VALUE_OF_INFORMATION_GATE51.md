# Gate 51 — Value of Information

Gate 51 uses the stochastic exploratory outcomes from Gate 50 and asks a different question: what is gained by observing which outcome occurred before choosing a downstream response?

Without information, one fixed response must be chosen for both possible exploratory outcomes. With information, the response can be conditioned on the observed successor state. In the verified witness, the best uninformed expected-utility numerator is 5, the informed value is 8, and therefore the finite value of information is 3.

Verified core claims:

- `gate51_best_uninformed_value`
- `gate51_informed_value`
- `gate51_value_of_information_eq_three`
- `gate51_value_of_information_positive`
- `gate51_information_can_be_valuable_despite_destabilization`
- `gate51_observation_strictly_improves_decision_value`

The result is relative to an explicit downstream utility. It is not Shannon information, mutual information, truth content, or a claim that every destabilizing observation is valuable.
