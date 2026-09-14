# Gate 75: Discounted Bellman Fixed Point

Gate 75 isolates the infinite-horizon algebra in a minimal exact Bellman witness:

```text
T(v) = 1 + v/2
```

Lean verifies:

```text
T(2) = 2
T(v) = v -> v = 2
T(x) - T(y) = (x - y)/2
```

Value iteration from zero begins:

```text
0, 1, 3/2, 7/4, 15/8, ...
```

and the residual to the fixed point is halved at every step.

## Interpretation

An infinite horizon need not mean uncontrolled epistemic drift. Discounting can turn repeated future reasoning into a stable fixed-point problem, with every Bellman update shrinking the remaining error.

## Boundary

This is the algebraic contraction core, not yet a Banach-space theorem for the full 4PEL belief-state controller.
