# Affine Threshold Crossing

Status: **VERIFIED** on `research/complex-coordinates` by the repository's Lean 4.31 CI build with `PEL4/ModalDynamicsAffineCrossing.lean` imported through `PEL4.lean`.

## Why this result matters

`Threshold-Straddle Geometry` proves an endpoint theorem: when a Lockean threshold bit changes, the before and after support masses lie on different threshold sides.

`Affine Threshold Crossing` strengthens that endpoint fact to a literal unit-interval crossing for the explicitly chosen rational affine path.

For rational endpoints `x,y` define

```text
gamma(t) = x + t * (y - x).
```

Lean verifies

```text
gamma(0) = x
gamma(1) = y.
```

If the endpoints straddle threshold `c`, there exists an explicit rational parameter

```text
t in [0,1]
```

such that

```text
gamma(t) = c.
```

For the increasing orientation `x < c <= y`, the witness is

```text
t = (c - x) / (y - x).
```

For the decreasing orientation `y < c <= x`, the directed path uses the algebraically equivalent backward form

```text
t = (x - c) / (x - y).
```

No Mathlib dependency is required; the proof uses Lean Core rational arithmetic.

## Belief-level consequence

Positive and negative support masses of a probabilistic belief provide two affine coordinates between the pre-update and post-update endpoints.

Lean verifies:

```text
belief value changes
->
at least one support coordinate has an affine threshold hit at some t in [0,1].
```

For a two-wall transition:

```text
both support coordinates have affine threshold hits,
possibly at different parameters.
```

Thus diagonal moves of the Threshold Square have two literal numerical crossing witnesses.

## Formal chain now closed

```text
support endpoints
  -> threshold straddling
  -> rational affine path
  -> explicit t in [0,1]
  -> exact threshold hit
  -> categorical FDE change.
```

## Current boundary

This is a genuine crossing theorem for the chosen affine interpolation, but it is not an abstract continuity theorem.

The project still does **not** quantify over arbitrary continuous paths or invoke a general intermediate-value theorem. The next gate studies a different question that is already available in the affine setting: when both support coordinates cross, are their crossing times simultaneous or sequential?

Working name: **Affine Threshold Crossing**.

## Novelty boundary

No novelty claim is made. The theorem is elementary mathematically; its role is structural. It closes a machine-checked bridge from probabilistic support endpoints through four-valued categorical change to an explicit threshold-crossing parameter.
