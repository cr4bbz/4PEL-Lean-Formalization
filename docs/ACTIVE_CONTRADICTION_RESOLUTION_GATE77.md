# Gate 77: Active Contradiction Resolution

Gate 77 treats a genuine 4PEL glut as a controllable epistemic state.

The witness begins with two independent support channels:

```text
positive support = 4/5
negative support = 4/5
threshold        = 3/4
```

so the proposition has value `B`.

A resolving experiment costs `1/5`. Its two equiprobable outcomes produce either:

```text
9/10 positive, 1/10 negative -> T
1/10 positive, 9/10 negative -> F
```

Classical resolution has utility `1`; remaining `B` or `N` has utility `0`. Therefore:

```text
stop in B     = 0
resolve Q     = 4/5
optimal action = resolveConflict
```

## Interpretation

Contradiction is not explosion and need not be a dead end. In this controller it is an epistemic condition that can make discriminating evidence worth purchasing. The policy does not decide in advance whether `T` or `F` should win; it pays to discover which side survives the resolving experiment.

## Boundary

The resolution utility and experiment are declared finite-model ingredients. The gate establishes possibility and decision structure, not a universal norm that every glut should be eliminated.
