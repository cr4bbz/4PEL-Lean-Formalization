# Gate 75: Discounted Bellman Fixed-Point Witness

Gate 75 tests the fixed-point idea behind discounted infinite-horizon control in a deliberately small executable model:

```text
T(v) = 1 + v/2
```

Lean verifies the candidate endpoint

```text
T(2) = 2
```

and the first value-iteration approximants from zero:

```text
0, 1, 3/2, 7/4, 15/8.
```

Their residual distances below `2` are

```text
2, 1, 1/2, 1/4, 1/8,
```

so the residual is exactly halved through the verified four-step window. Lean also checks that none of the displayed pre-limit approximants is a fixed point, whereas `2` is.

## Interpretation

Discounting can make repeated future planning settle toward a stable target rather than keep adding equal weight forever. In this witness, each Bellman update removes half of the remaining error.

## Boundary

This is a finite executable contraction witness. It does **not** yet prove uniqueness over every rational value, convergence for arbitrary iteration count, a Banach fixed-point theorem, or a complete infinite-horizon 4PEL belief-state controller. Those are later generalization targets rather than Gate-75 results.
