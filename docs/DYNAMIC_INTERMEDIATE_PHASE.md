# Affine Intermediate-Phase Geometry

Status: **active build gate** on `research/preface-case-study`.

Do not mark `PEL4/ModalDynamicsIntermediatePhase.lean` compiler-verified until a fresh local Lean 4.31 `lake build` succeeds with the module imported through `PEL4.lean`.

## Question

Affine Crossing-Order Geometry verifies that a two-wall affine support transition has two unique crossing times:

```text
tp = positive-support threshold hit
tn = negative-support threshold hit.
```

If they are unequal, what categorical four-valued phase occupies the interval between them?

## Rational midpoint witness

For sequential crossings the module chooses the explicit rational midpoint

```text
tm = (tp + tn) / 2.
```

The first target theorem proves

```text
tp < tn -> tp < tm < tn
tn < tp -> tn < tm < tp.
```

No density or topology library is required; this is direct rational arithmetic.

## Monotone affine coordinates

For

```text
gamma(t) = x + t * (y - x)
```

the module targets strict parameter monotonicity:

```text
x < y and t < s -> gamma(t) < gamma(s)
y < x and t < s -> gamma(s) < gamma(t).
```

Combining monotonicity with the unique crossing time yields an exact side theorem:

```text
before the crossing -> same threshold bit as the source endpoint
after the crossing  -> same threshold bit as the target endpoint.
```

## Intermediate vertex

Let

```text
source = (source positive bit, source negative bit)
target = (target positive bit, target negative bit).
```

If the positive wall is crossed first, the target intermediate state is

```text
(target positive bit, source negative bit).
```

If the negative wall is crossed first, the target intermediate state is

```text
(source positive bit, target negative bit).
```

For opposite endpoints these states are adjacent to both source and target in the Threshold Square.

The concrete diagonal table is:

```text
N -> B : positive first -> T ; negative first -> F
B -> N : positive first -> F ; negative first -> T
T -> F : positive first -> N ; negative first -> B
F -> T : positive first -> B ; negative first -> N.
```

Thus a nonsimultaneous diagonal transition should decompose into two one-wall phases along the affine support interpolation.

## Simultaneous exception

If

```text
tp = tn,
```

Crossing-Order Geometry already proves that the two-dimensional support path hits

```text
(c,c)
```

at one common parameter. In this case there is no open interval between the two wall events, so no sequential intermediate vertex is forced by the ordering argument.

## Semantic boundary

The interpolated object is a pair of support masses, not yet a full interpolated `Model` satisfying all probability and admissibility constraints.

Therefore the intended theorem says:

```text
the affine support interpolation occupies an intermediate FDE threshold phase.
```

It does **not** yet say:

```text
there exists an actual intermediate admissible probabilistic model update realizing that phase.
```

That stronger realizability question is a natural later gate.

Working name: **Affine Intermediate-Phase Geometry**.

## Novelty boundary

No novelty claim is made. The mathematical ingredients are elementary. The project-level contribution is the formally checked bridge from two-coordinate crossing order to the exact intermediate four-valued phase hidden by a diagonal endpoint projection.
