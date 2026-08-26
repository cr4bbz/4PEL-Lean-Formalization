# Threshold Square Geometry

Status: **VERIFIED** on `research/complex-coordinates` by the repository's Lean 4.31 CI build with `PEL4/ModalDynamicsGeometry.lean` imported through `PEL4.lean`.

## Core representation

A four-valued epistemic status already has two Boolean coordinates:

```text
N = (0,0)
T = (1,0)
F = (0,1)
B = (1,1)
```

The first coordinate records whether positive support is on or above threshold; the second does the same for negative support.

This turns the categorical state space into the Boolean square:

```text
N ---- T
|      |
|      |
F ---- B
```

## Threshold-wall count

`thresholdWallCount a b` counts how many coordinates differ between two FDE values.

Lean verifies:

```text
thresholdWallCount(a,b) is always 0, 1, or 2.
thresholdWallCount(a,b) = 0 iff a = b.
thresholdWallCount(a,b) = 2 iff both coordinates differ.
```

Interpretation:

```text
0 -> same categorical status
1 -> exactly one threshold side changes
2 -> both threshold sides change
```

The edge pairs are:

```text
N <-> T
N <-> F
T <-> B
F <-> B
```

The diagonals are:

```text
T <-> F
N <-> B.
```

## Connection to robustness

Threshold-Side Robustness proves that a probabilistic belief is invariant exactly when both threshold bits are invariant.

The geometry module verifies the geometric restatement:

```text
belief robust at a point
iff
thresholdWallCount(before, after) = 0.
```

It also proves that every compositionally robust modal formula has zero categorical displacement under its designated conditionalization.

## Connection to complete reachability

The six-world reachability family realizes every ordered pair of FDE values by safe probability-only conditionalization.

The geometry gate verifies:

```text
displacement(realized source -> target)
=
displacement(source,target).
```

Hence admissible conditionalization realizes all three combinatorial displacement classes:

```text
0-wall transitions
1-wall transitions
2-wall transitions.
```

## Current boundary

The word "wall" is compiler-verified at the combinatorial level. The model still has rational endpoint probability measures rather than a formal continuous path between them.

The next gate, `PEL4/ModalDynamicsThresholdCrossing.lean`, reconnects these walls to the numerical support masses. Its target theorem says that a changed threshold bit is equivalent to endpoint masses straddling the Lockean threshold. That order-theoretic straddling result is the intended bridge toward a later genuine continuity theorem.

## Research payoff

The dynamic results now support a three-level picture:

```text
probability state
    -> threshold cell / side pair
        -> FDE vertex in the Boolean square.
```

Raw probability may vary within a categorical cell without changing epistemic status. Categorical change is measured by coordinate displacement. Complete reachability describes which vertices can be connected by admissible updates; robustness identifies the zero-displacement class.

Working name: **Threshold Square Geometry**.

## Novelty boundary

No novelty claim is made. The natural comparison targets include Hamming geometry on bilattice values, threshold classifiers, probabilistic belief revision, and four-valued dynamic epistemic systems.
