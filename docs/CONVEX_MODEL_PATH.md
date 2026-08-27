# Convex Strong Model Path

Status: **VERIFIED**

## Goal

`PEL4/ConvexModelPath.lean` lifts the verified finite probability-simplex path
into complete 4-PEL models.

The semantic skeleton is held fixed:

```text
worlds
R
val
c
```

Only the local probability field varies.

For endpoint local weight fields `q_0` and `q_1` satisfying
`FiniteWeightDistribution` at every agent/world pair, and rational

```text
0 <= t <= 1,
```

define

```text
q_t(i,w,x) = (1-t) q_0(i,w,x) + t q_1(i,w,x).
```

C17C proves that each local `q_t(i,w,.)` is again a valid finite weight
distribution. C17D packages those distributions into a full
`StrongProbabilityModel`.

## Verified results

A fresh local Lean 4.31 `lake build` succeeded with this module imported through
`PEL4.lean`.

Lean therefore verifies:

```text
convexStrongModelAt ... t : StrongProbabilityModel W Ag Atom
```

for every rational unit-interval parameter, together with exact preservation of

```text
worlds
R
val
c
```

along the path.

Every fixed local event has affine probability mass:

```text
mu_t(S) = (1-t) * mu_0(S) + t * mu_1(S).
```

The relevant theorem is `convexStrongModelAt_eventMass`.

## What this closes

The project now has an actual rational path of complete probabilistically
certified 4-PEL models for any two weight-generated endpoint distributions on
the same semantic skeleton:

```text
finite probability integrity
-> weight-generated measures
-> convex probability simplex
-> convex strong model path.
```

Thus the probability-simplex geometry is not merely interpretive. Every
rational point on the segment is represented by a full strong model.

## Scientific boundary

The event-mass theorem is deliberately stated for a **fixed event** `S`.
For an arbitrary probability-sensitive modal formula `phi`, the set of worlds
where `evalModal phi` has positive or negative support may itself change with
the path parameter. Therefore C17D does not yet claim that
`modalPositiveBeliefMass` or `modalNegativeBeliefMass` is affine for every
modal formula.

Nor does C17D prove that every intermediate model is itself obtained by an
admissible conditionalization of the source model. A model-valued convex path
and an update-generated path are distinct notions.

That formula-level lift is now verified in `PEL4/ConvexModelSupport.lean` for
the full probability-free modal fragment.  `PEL4/ComplexModelPath.lean` and
`PEL4/ComplexModelCrossing.lean` connect it to the earlier threshold-crossing
and intermediate-phase geometry.  The maximal path-invariant fragment
containing selected `bel` formulas remains open.
