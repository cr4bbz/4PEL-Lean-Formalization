# Affine Crossing-Order Geometry

Status: **VERIFIED** on `research/complex-coordinates` by the repository's Lean 4.31 CI build with `PEL4/ModalDynamicsCrossingOrder.lean` imported through `PEL4.lean`.

## Motivation

Affine Threshold Crossing proves that a two-wall belief transition has a positive-support threshold hit and a negative-support threshold hit somewhere on the rational unit interval.

The remaining ambiguity is temporal:

```text
which threshold wall is crossed first?
```

That question is meaningful only if the affine hit parameter is intrinsic rather than an arbitrary existential witness. The module therefore first proves uniqueness.

## Unique affine crossing time

For a nonconstant affine path

```text
gamma(t) = x + t * (y - x)
```

Lean verifies that if

```text
gamma(t) = c
gamma(s) = c
x != y
```

then

```text
t = s.
```

Threshold-straddling endpoints are automatically distinct, so every straddling affine segment has a unique threshold-crossing time.

## Two-coordinate crossing pair

For a two-wall transition, let

```text
tp = unique positive-support crossing time
tn = unique negative-support crossing time.
```

Both lie in `[0,1]`. Linear order on the rationals gives the exhaustive temporal classification

```text
tp < tn   positive wall first
tp = tn   simultaneous crossing
tn < tp   negative wall first.
```

Lean verifies propositionally that every two-wall conditionalized belief transition admits such a crossing pair together with exactly this trichotomy.

## Geometric meaning of simultaneity

Lean also verifies that simultaneous crossing is equivalent to the existence of one parameter `t` such that both affine support coordinates equal the Lockean threshold:

```text
P+(t) = c
P-(t) = c.
```

In the two-dimensional support plane this is exactly passage through the wall intersection

```text
(c,c).
```

Thus simultaneous crossing is geometrically special, not merely equality of two bookkeeping parameters.

## Relation to FDE diagonal transitions

The Threshold Square has two diagonals:

```text
N <-> B
T <-> F.
```

A two-wall update realizes one of these diagonal displacements at the categorical endpoint level. Crossing-order geometry refines such a diagonal into temporal information about the underlying affine support interpolation.

The next gate is the **intermediate-vertex classification**: when `tp != tn`, the rational interval between the two unique crossing times should occupy the adjacent FDE phase obtained by changing exactly the first-crossed threshold coordinate. For example, along the support interpolation:

```text
N -> B, positive first  : intermediate T
N -> B, negative first  : intermediate F
T -> F, positive first  : intermediate N
T -> F, negative first  : intermediate B.
```

The reverse diagonal orientations have the corresponding reversed table.

## Current boundary

This remains an affine rational support-path result. The affine interpolation is a constructed path through support-mass space; it is **not yet** a proof that every intermediate point is itself realized by an admissible probabilistic model update. Nor does the result quantify over arbitrary continuous paths.

Working name: **Affine Crossing-Order Geometry**.

## Novelty boundary

No novelty claim is made. The mathematical ingredients are elementary. Their role is to expose temporal structure hidden by the four-valued endpoint projection and to prepare a precise bridge from diagonal FDE displacement to intermediate epistemic phases.
