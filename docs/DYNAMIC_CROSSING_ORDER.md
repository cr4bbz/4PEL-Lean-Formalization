# Affine Crossing-Order Geometry

Status: **active build gate** on `research/preface-case-study`.

Do not mark `PEL4/ModalDynamicsCrossingOrder.lean` compiler-verified until a fresh local Lean 4.31 `lake build` succeeds with the module imported through `PEL4.lean`.

## Motivation

Affine Threshold Crossing proves that a two-wall belief transition has a positive-support threshold hit and a negative-support threshold hit somewhere on the rational unit interval.

The remaining ambiguity is temporal:

```text
which threshold wall is crossed first?
```

That question is meaningful only if the affine hit parameter is intrinsic rather than an arbitrary existential witness. The new module therefore first proves uniqueness.

## Unique affine crossing time

For a nonconstant affine path

```text
gamma(t) = x + t * (y - x)
```

if

```text
gamma(t) = c
gamma(s) = c
x != y
```

then the target theorem proves

```text
t = s.
```

Threshold-straddling endpoints are automatically distinct, so every straddling affine segment should have a unique threshold-crossing time.

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

## Geometric meaning of simultaneity

The simultaneous case should be equivalent to the existence of one parameter `t` such that both affine support coordinates equal the Lockean threshold:

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

A two-wall update realizes one of these diagonal displacements at the categorical level. Crossing-order geometry refines such a diagonal into temporal information about the underlying support path.

The next natural theorem, if this gate compiles, is the **intermediate-vertex classification**: when `tp != tn`, the interval between the two crossing times should occupy one of the adjacent FDE vertices. Which vertex appears depends on the diagonal orientation and on which support wall crosses first.

## Current boundary

This remains an affine rational path result. It does not yet assert anything about arbitrary continuous paths.

Working name: **Affine Crossing-Order Geometry**.

## Novelty boundary

No novelty claim is made. The mathematical ingredients are elementary. Their role is to expose temporal structure hidden by the four-valued endpoint projection and to prepare a precise bridge from diagonal FDE displacement to intermediate epistemic phases.
