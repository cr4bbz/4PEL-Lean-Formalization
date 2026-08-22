# Weight-Generated Finite Probability

Status: **ACTIVE BUILD GATE**

## Goal

`PEL4/WeightGeneratedProbability.lean` turns the verified finite-probability
integrity contract into a constructive measure generator.

For a finite accessibility support `R` and rational point weights `q`, define

```text
mu_q(S) = sum over x in R of (if x in S then q(x) else 0).
```

The iteration is deliberately support-driven rather than event-list-driven.
Thus event order and duplicate presentation do not affect the generated mass.

## Distribution contract

`FiniteWeightDistribution R q` requires:

```text
R is duplicate-free
q(x) >= 0 for every x in R
mu_q(R) = 1
```

The target theorem is:

```text
FiniteWeightDistribution R q
->
FiniteProbabilityIntegrity (weightGeneratedMeasure R q) R.
```

If the gate compiles, the following integrity laws are inherited generically:

```text
nonnegative event mass
set extensionality
monotonicity under inclusion
finite additivity on disjoint events
empty-event mass zero
total support mass one.
```

## Why this matters

C17A verified a stronger semantic contract but did not yet explain where valid
measures come from.  C17B supplies the constructive source.  Concrete models
can then be promoted by exhibiting normalized nonnegative world weights rather
than reproving the probability laws ad hoc at every world.

## Next gate after verification

The intended next step is convex rational interpolation on a fixed support:

```text
q_t(x) = (1-t) q_0(x) + t q_1(x),   0 <= t <= 1.
```

The key target will be:

```text
FiniteWeightDistribution R q_0
and FiniteWeightDistribution R q_1
->
FiniteWeightDistribution R q_t.
```

That theorem would make the finite probability simplex an explicit formal path
space and prepare the lift from affine support trajectories to genuine
intermediate 4-PEL models.
