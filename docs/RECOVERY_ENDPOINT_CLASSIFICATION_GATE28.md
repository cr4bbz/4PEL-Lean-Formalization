# Gate 28 — Recovery Endpoint Classification

## Question

Gate 27 proves that every infinite trajectory satisfying the abstract Gate-26 descent contract eventually becomes constant in its Boolean recovery status. Gate 28 asks what that eventual constant is.

The key distinction is:

- **eventual stability**: after some finite index, recovery status no longer changes;
- **eventual Recovery**: after some finite index, recovery status is specifically `true`.

Gate 27 establishes the first, not the second.

## Formal endpoint predicate

`EventuallyRecoveryStatus sys trajectory target` means that there is some index `N` such that every later state has recovery status `target`.

Because the status is Boolean, every eventually stable trajectory has exactly one of two endpoint phases:

1. eventually always Recovery (`true`), or
2. eventually always Non-Recovery (`false`).

The theorem

`recoveryTrajectory_endpoint_classification`

formalizes the exhaustive dichotomy, while

`eventuallyRecoveryStatus_exclusive`

shows that the two asymptotic endpoint statuses cannot both hold on the same trajectory.

The combined theorem

`recoveryTrajectory_exactly_one_endpoint`

therefore gives an exact two-way endpoint classification for every valid infinite descent trajectory.

## Negative result: stability does not force Recovery

Gate 28 deliberately includes two minimal one-state descent systems.

- `gate28RecoverySystem` has status permanently `true`.
- `gate28NonRecoverySystem` has status permanently `false`.

Both have zero potential and permit only status-preserving evolution. Their shared infinite unit trajectory satisfies the Gate-26 descent contract.

Thus both asymptotic endpoints are consistent with the abstract theory.

The theorem

`gate28_eventual_stability_does_not_force_recovery`

makes the central limitation explicit: a trajectory can satisfy eventual recovery stability while failing to be eventually Recovery.

## Interpretation

The descent framework establishes a form of **finite variation**, not a truth-directed convergence theorem.

It guarantees that a valid process cannot oscillate indefinitely between Recovery and Non-Recovery, but it does not by itself privilege the Recovery phase as the destination.

In the ten-year-old robot picture: the robot eventually stops changing the colour of its recovery light, but Gate 27 alone does not tell us whether the final light is green or red.

This separates two research questions that should not be conflated:

1. Why must recovery status eventually stop changing?
2. Under what stronger learning assumptions must the stable endpoint specifically be Recovery?

Gate 28 answers the first framework question completely and leaves the second as a later attractor problem.

## Boundary to Gate 29

Gate 28 does **not** yet claim path dependence from a shared initial state. Its two endpoint witnesses are separate minimal systems.

Gate 29 should ask the stronger question: can one and the same initial epistemic state admit two valid update trajectories with different stable recovery endpoints?

That would move from endpoint possibility to genuine epistemic path dependence.
