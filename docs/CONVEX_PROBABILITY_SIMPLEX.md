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

This module alone is a distribution-level theorem.  Its successor,
`PEL4/ConvexModelPath.lean`, packages every intermediate distribution into a
complete strong 4-PEL model while preserving the relational, valuation, and
threshold components required by the semantic architecture.

## Completed successor gate

`PEL4/ConvexModelPath.lean` constructs the model-valued convex path with fixed
`R`, `val`, and `c`.  `PEL4/ConvexModelSupport.lean` then proves affine positive
and negative formula-support masses for probability-free formulas, and
`PEL4/ComplexModelCrossing.lean` realizes the crossing classification on those
complete models.
