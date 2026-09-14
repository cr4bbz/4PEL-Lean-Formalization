# Gate 60 — Noisy Epistemic Observation

## Question

What remains of the Gate-57 POMDP bridge when Recovery is an unreliable observation rather than a perfect hidden-state label?

## Verified result

`PEL4.NoisyEpistemicObservation` introduces `FiniteNoisyEpistemicPOMDP` with a stochastic hidden-state transition process and a separate finite observation likelihood kernel.

This keeps three probability layers distinct:

1. probabilities internal to a 4PEL model;
2. transition probabilities between hidden epistemic states;
3. observation likelihoods emitted by the sensor.

The Gate-60 witness uses a 90/10 sensor. After exploration from the symmetric prior:

```text
P(recovery signal) = 1/2
P(robust | recovery signal) = 9/10
P(destabilized | recovery signal) = 1/10
```

The complementary Non-Recovery signal reverses those posterior weights.

Key theorems:

- `gate60_recovery_signal_probability`
- `gate60_recovery_posterior`
- `gate60_nonRecovery_posterior`
- `gate60_recovery_signal_not_oracle`
- `gate60_recovery_is_evidence_not_oracle`

Thus a Recovery signal can strongly support the Gate-54 truth-certified robust state without identifying it with certainty.

## Boundary

The 90/10 reliability is a formal witness, not an empirical calibration claim. This gate does not yet optimize sensor choice, prove repeated-learning convergence, or handle model misspecification.
