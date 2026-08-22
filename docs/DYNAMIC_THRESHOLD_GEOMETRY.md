# Threshold Square Geometry

Status: **active build gate** on `research/preface-case-study`.

Do not mark `PEL4/ModalDynamicsGeometry.lean` compiler-verified until a fresh local Lean 4.31 `lake build` succeeds with the module imported through `PEL4.lean`.

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

Target verified range:

```text
0, 1, or 2 only.
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

The geometry module restates this as:

```text
belief robust at a point
iff
thresholdWallCount(before, after) = 0.
```

It also proves that every compositionally robust modal formula has zero categorical displacement under its designated conditionalization.

## Connection to complete reachability

The six-world reachability family already realizes every ordered pair of FDE values by safe probability-only conditionalization.

The geometry gate packages this as:

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

## What is not yet claimed

The word "wall" is currently combinatorial. The model has rational endpoint probability measures, not a formal continuous path between them.

A later theorem could introduce a parameterized path of positive/negative support masses and ask whether a transition of wall count `k` forces at least `k` threshold-equality events along the path. That would require an ordered/continuous path layer and should not be inferred from the present finite endpoint theorem.

## Research payoff

The dynamic results now suggest a three-level picture:

```text
probability state
    -> threshold cell / side pair
        -> FDE vertex in the Boolean square.
```

Raw probability may vary within a categorical cell without changing epistemic status. Categorical change is measured by coordinate displacement. Complete reachability describes which vertices can be connected by admissible updates; robustness identifies the zero-displacement class.

Working name: **Threshold Square Geometry**.

## Novelty boundary

No novelty claim is made. The natural comparison targets include Hamming geometry on bilattice values, threshold classifiers, probabilistic belief revision, and four-valued dynamic epistemic systems.
