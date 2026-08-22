# Affine Threshold Crossing

Status: **active build gate** on `research/preface-case-study`.

Do not mark `PEL4/ModalDynamicsAffineCrossing.lean` compiler-verified until a fresh local Lean 4.31 `lake build` succeeds with the module imported through `PEL4.lean`.

## Why this gate exists

`Threshold-Straddle Geometry` proves an endpoint theorem: when a Lockean threshold bit changes, the before and after support masses lie on different threshold sides.

The next question is stronger:

```text
can we exhibit an actual parameter value between the two endpoints where the support mass equals the threshold?
```

For arbitrary continuous paths that is an intermediate-value question. But for the simplest path, affine interpolation, Lean Core already contains enough rational arithmetic to construct the crossing explicitly without adding Mathlib.

## Affine path

For rational endpoints `x,y` define

```text
gamma(t) = x + t * (y - x).
```

The module verifies the endpoint equations as proof targets:

```text
gamma(0) = x
gamma(1) = y.
```

If `x < c <= y`, the candidate hit parameter is

```text
t = (c - x) / (y - x).
```

If `y < c <= x`, the directed path from `x` to `y` instead uses

```text
t = (x - c) / (x - y).
```

The target theorems prove in both orientations:

```text
0 <= t <= 1
and
gamma(t) = c.
```

Hence endpoint threshold straddling should imply

```text
exists t : Rat,
  0 <= t and t <= 1 and gamma(t) = c.
```

## Belief-level consequence

Positive and negative support masses of a probabilistic belief give two affine coordinates between the pre-update and post-update endpoints.

Combining the new affine theorem with the verified straddling theorem yields the target consequence:

```text
belief value changes
->
at least one support coordinate has an affine threshold hit at some t in [0,1].
```

For a two-wall transition the target statement is stronger:

```text
both support coordinates have affine threshold hits,
possibly at different parameters.
```

Thus diagonal moves of the Threshold Square acquire two explicit numerical crossing witnesses.

## What this does and does not prove

This gate would be a genuine unit-interval crossing theorem for the explicitly chosen rational affine interpolation.

It does **not** yet formalize:

```text
Continuous gamma
```

as an abstract topological predicate, nor does it prove an intermediate-value theorem for every continuous support path. No claim about arbitrary paths should be inferred from the affine construction.

The distinction is:

```text
endpoint straddling          VERIFIED
explicit affine crossing     ACTIVE BUILD GATE
general continuous crossing  OPEN
```

## Dependency decision

The gate uses only Lean Core rational lemmas, including rational division cancellation and order transport across positive denominators. No Mathlib dependency is introduced.

If this builds, it substantially reduces the immediate need for a topology dependency: the central geometric phenomenon can already be studied constructively in the affine case.

Working name: **Affine Threshold Crossing**.

## Novelty boundary

No novelty claim is made. The theorem is elementary mathematically; its value in the project is structural. It closes a formally checked bridge from probabilistic support endpoints through categorical four-valued change to an explicit threshold-crossing parameter.
