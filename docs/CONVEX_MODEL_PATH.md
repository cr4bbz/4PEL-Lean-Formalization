# Convex Strong Model Path

Status: **ACTIVE BUILD GATE**

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

C17C already proves that each local `q_t(i,w,.)` is again a valid finite weight
distribution. C17D packages those distributions into a full
`StrongProbabilityModel`.

## Principal targets

The module targets:

```text
convexStrongModelAt ... t : StrongProbabilityModel W Ag Atom
```

and proves that along this model-valued path:

```text
worlds = constant
R      = constant
val    = constant
c      = constant
```

while every fixed local event has affine probability mass:

```text
mu_t(S) = (1-t) * mu_0(S) + t * mu_1(S).
```

## Scientific boundary

The event-mass theorem is deliberately stated for a **fixed event** `S`.
For an arbitrary probability-sensitive modal formula `phi`, the set of worlds
where `evalModal phi` has positive or negative support may itself change with
the path parameter. Therefore this gate does not yet claim that
`modalPositiveBeliefMass` or `modalNegativeBeliefMass` is affine for every
modal formula.

The next formula-level lift should begin with atomic propositions or a proved
path-invariant formula fragment, where the underlying support events remain
fixed.

## Intended consequence after verification

A successful build would establish an actual rational path of complete,
probabilistically certified 4-PEL models:

```text
finite probability integrity
-> weight-generated measures
-> convex probability simplex
-> convex strong model path.
```

That would close the previously explicit gap between affine support
interpolation and the existence of genuine intermediate models, while leaving
the separate formula-event invariance question visible for the next gate.
