# Threshold-Straddle Geometry

Status: **VERIFIED** on `research/complex-coordinates` by the repository's Lean 4.31 CI build with `PEL4/ModalDynamicsThresholdCrossing.lean` imported through `PEL4.lean`.

## Question

`Threshold Square Geometry` classifies categorical endpoint displacement by the number of changed positive/negative threshold bits. Threshold-Straddle Geometry reconnects those categorical walls to the underlying support masses.

For threshold `c` and rational endpoint masses `x,y`, define

```text
ThresholdStraddles c x y
```

in core-compatible form by

```text
(c <= x and not (c <= y))
or
(c <= y and not (c <= x)).
```

On the ordered rationals this says that one endpoint reaches or exceeds the threshold while the other remains below it.

Lean verifies the exact equivalence

```text
decide(c <= x) != decide(c <= y)
iff
ThresholdStraddles c x y.
```

Thus a categorical threshold-bit flip has an exact numerical endpoint witness.

## Belief-level decomposition

Probabilistic belief has two support coordinates:

```text
M+ = positive support mass
M- = negative support mass.
```

For every admissible conditionalization, Lean verifies that the Boolean-square wall count decomposes into the two one-dimensional support wall counts:

```text
wallCount(B phi before, B phi after)
=
posWallCount + negWallCount.
```

Hence:

```text
0 walls -> neither M+ nor M- straddles threshold
1 wall  -> exactly one of M+, M- straddles threshold
2 walls -> both M+ and M- straddle threshold.
```

A further verified theorem states:

```text
B phi changes categorically
->
M+ straddles threshold or M- straddles threshold.
```

So every genuine belief-status change has a numerical witness in at least one support coordinate.

## Relation to robustness

Threshold-Side Robustness and Threshold-Straddle Geometry now describe the same dynamic boundary from complementary directions:

```text
threshold bits unchanged -> belief value invariant
no support straddling     -> zero categorical displacement
categorical change        -> at least one support coordinate straddles threshold.
```

Together with Complete Dynamic Epistemic Reachability and Threshold Square Geometry, this closes the finite endpoint chain

```text
support masses
  -> threshold sides
  -> Boolean-square wall count
  -> FDE belief status.
```

## Current boundary

This result is still endpoint order theory. It does **not** yet prove that a continuously varying support mass attains the threshold at an intermediate parameter.

The next genuinely stronger statement would have the form

```text
continuous f : [0,1] -> support mass
f(0) and f(1) straddle c
->
exists t, f(t) = c.
```

That requires a path/continuity layer and an intermediate-value principle. The verified straddling theorem supplies the exact endpoint hypothesis for such an extension.

Working name: **Threshold-Straddle Geometry**.

## Novelty boundary

No novelty claim is made. The current result is an internal structural theorem connecting Lockean threshold decisions, rational support order, and the verified Boolean-square geometry. A publication-level novelty assessment still requires systematic comparison with threshold belief revision, bilattice-valued dynamics, and related four-valued epistemic systems.
