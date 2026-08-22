# Convex Model Support Lift

Status: **ACTIVE BUILD GATE**

## Goal

`PEL4/ConvexModelSupport.lean` lifts the verified fixed-event affine theorem from
C17D to formula-defined positive and negative support masses for the
probability-free modal fragment.

The central observation is that `ModalProbabilityFree` formulas contain no
`bel` constructor. Their semantics therefore depends only on accessibility and
atomic valuation. Along `convexStrongModelAt`, both fields remain fixed.

## Generic skeleton theorem

The module first targets the reusable result:

```text
same R
and same val
and ModalProbabilityFree phi
->
evalModal n w phi = evalModal m w phi.
```

This generalizes the earlier conditionalization-specific invariance theorem to
arbitrary model pairs sharing the non-probabilistic modal skeleton.

It then proves that the positive and negative support events are extensionally
and list-wise identical between such models.

## Main affine support targets

For the complete strong model path `M_t`, the target formulas are:

```text
modalPositiveBeliefMass M_t i w phi
=
(1-t) * modalPositiveBeliefMass M_0 i w phi
+ t * modalPositiveBeliefMass M_1 i w phi
```

and symmetrically for negative support, whenever

```text
ModalProbabilityFree phi.
```

If compiler-verified, this establishes that the actual signed support
coordinates of every probability-free formula are affine along a path of
complete probabilistically certified 4-PEL models.

## Scientific significance

C17D supplied:

```text
complete strong model path
+ affine mass of every fixed event.
```

C17E targets the missing formula-level bridge:

```text
probability-free formula
-> support events fixed along the path
-> positive and negative support masses affine
-> existing threshold crossing geometry applies at model level.
```

Formulas containing probabilistic belief remain outside this theorem because
their own evaluation, and therefore their support events, may vary with the
probability path.

## Next gate after verification

Reuse the existing threshold-straddling, unique crossing-order, and midpoint
phase theorems with these model-level affine support identities. The intended
result is a genuine strong-model phase theorem for probability-free embedded
formulas, with a separate later investigation of formulas containing `bel`.
