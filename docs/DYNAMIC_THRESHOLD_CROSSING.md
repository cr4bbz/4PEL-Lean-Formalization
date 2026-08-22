# Threshold-Straddle Geometry

Status: **active build gate** on `research/preface-case-study`.

Do not mark `PEL4/ModalDynamicsThresholdCrossing.lean` compiler-verified until a fresh local Lean 4.31 `lake build` succeeds with the module imported through `PEL4.lean`.

## Question

`Threshold Square Geometry` classifies categorical endpoint displacement by the number of changed positive/negative threshold bits. The next question is numerical:

```text
what must happen to the underlying support masses when one of those bits changes?
```

For threshold `c` and rational endpoint masses `x,y`, define

```text
ThresholdStraddles c x y
```

by

```text
x < c <= y
or
y < c <= x.
```

The target core theorem is the exact equivalence

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

For one admissible conditionalization, the proposed theorem decomposes the Boolean-square wall count into two one-dimensional support wall counts:

```text
wallCount(B phi before, B phi after)
=
posWallCount + negWallCount.
```

This yields the endpoint classification:

```text
0 walls -> neither M+ nor M- straddles threshold
1 wall  -> exactly one of M+, M- straddles threshold
2 walls -> both M+ and M- straddle threshold.
```

A further target theorem states that any genuine categorical belief change must therefore be accompanied by threshold straddling on at least one support coordinate.

## Relation to robustness

Threshold-Side Robustness says that unchanged threshold bits protect categorical belief value. Threshold-Straddle Geometry supplies the numerical converse view:

```text
no support straddling -> zero categorical displacement
categorical change    -> at least one support straddles threshold.
```

The two results therefore describe the same boundary from Boolean and ordered-rational perspectives.

## Relation to continuity

This gate deliberately stops at endpoint order theory. It does **not** yet prove that a continuously varying support mass attains the threshold at an intermediate parameter.

The later continuous statement would have the form:

```text
continuous f : [0,1] -> support mass
f(0) < c <= f(1)
->
exists t, f(t) = c.
```

That requires a topology/continuity layer and an intermediate-value theorem. The present straddling theorem is intended to provide the exact endpoint hypothesis for such a future extension.

Working name: **Threshold-Straddle Geometry**.

## Novelty boundary

No novelty claim is made. The immediate result is an internal structural theorem connecting Lockean threshold decisions, rational support order, and the previously verified Boolean-square geometry.
