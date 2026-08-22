# Convex Probability Simplex

Status: **VERIFIED**

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

The principal theorem is:

```text
FiniteWeightDistribution R q_0
and FiniteWeightDistribution R q_1
and 0 <= t <= 1
->
FiniteWeightDistribution R q_t.
```

A fresh local Lean 4.31 `lake build` compiled the module through the root
`PEL4.lean` import.

## Verified affine event-mass statement

The module also proves the reusable identity

```text
weightedEventMass R q_t S
=
(1 - t) * weightedEventMass R q_0 S
+ t * weightedEventMass R q_1 S.
```

Thus every event mass moves affinely along the same parameter as the underlying
weight vector.

This provides the formal bridge from the finite probability simplex to the
previously verified affine threshold-crossing geometry.

## Verified consequence

Together with C17A and C17B, the build establishes:

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

## Next gate

Construct a model-valued convex path with fixed `R`, `val`, and `c`, using the
verified weight-generated measures locally. Then prove that positive and
negative belief-support masses along that model path coincide with the affine
support paths already used by the crossing-order and intermediate-phase modules.
