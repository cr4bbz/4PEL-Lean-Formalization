# Convex Probability Simplex

Status: **ACTIVE BUILD GATE**

## Goal

`PEL4/ConvexProbabilitySimplex.lean` studies rational convex interpolation of two
verified finite weight distributions on the same duplicate-free support.

For

```text
0 <= t <= 1
```

define

```text
q_t(x) = (1 - t) q_0(x) + t q_1(x).
```

The principal target is:

```text
FiniteWeightDistribution R q_0
and FiniteWeightDistribution R q_1
and 0 <= t <= 1
->
FiniteWeightDistribution R q_t.
```

## Stronger affine event-mass statement

The module also targets the reusable identity

```text
weightedEventMass R q_t S
=
(1 - t) * weightedEventMass R q_0 S
+ t * weightedEventMass R q_1 S.
```

Thus every event mass should move affinely along the same parameter as the
underlying weight vector.

If compiler-verified, this provides the formal bridge from the finite
probability simplex to the previously verified affine threshold-crossing
geometry.

## Intended consequence

Together with C17A and C17B, a successful build would establish:

```text
valid rational endpoint distributions
-> full rational line segment remains probabilistically valid
-> every intermediate point generates FiniteProbabilityIntegrity
-> every event mass follows an affine path.
```

This is not yet a theorem that every intermediate point is a complete 4-PEL
model. The next gate must package interpolated local distributions into a model
while preserving the relational, valuation, and threshold components required
by the semantic architecture.
