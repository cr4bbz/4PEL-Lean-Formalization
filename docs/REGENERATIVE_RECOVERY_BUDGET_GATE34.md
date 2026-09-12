# Gate 34 — Regenerative Recovery Budgets

## Research question

Earlier Recovery gates used a finite natural-valued potential that could only be consumed. Gate 34 asks what survives when an update may also create new epistemic resource.

The answer is an accounting theorem rather than monotone descent.

For a transition `s -> t`, let

- `c(s,t)` be the unit Recovery-status change cost,
- `Phi(s)` be remaining Recovery potential,
- `rho(s,t)` be newly regenerated resource.

The local contract is

```text
c(s,t) + Phi(t) <= Phi(s) + rho(s,t).
```

Along a finite path this telescopes to

```text
Recovery changes + final potential
  <= initial potential + total regeneration.
```

Therefore

```text
Recovery changes <= initial potential + total regeneration.
```

If an independent argument bounds all resource creation by `R`, then

```text
Recovery changes <= initial potential + R.
```

## Relation to Gate 26

Gate 26 is exactly the zero-regeneration special case `rho = 0`. Gate 34 therefore extends rather than replaces the finite-descent theory.

The conceptual change is important:

```text
Gate 26: potential is a depleting flip budget.
Gate 34: potential participates in a resource balance sheet.
```

A Recovery flip may now occur after the original budget would have been exhausted, but it must be funded by explicitly created resource.

## Sharp witness

The verified three-state witness starts with one unit of potential:

```text
(start, Recovery, Phi=1)
  -- regenerate 1 -->
(regenerated, Non-Recovery, Phi=1)
  -- regenerate 0 -->
(finish, Recovery, Phi=0)
```

It contains two Recovery-status flips, while

```text
initial potential = 1
total regeneration = 1
change count = 2
```

so the bound is attained exactly:

```text
2 = 1 + 1.
```

This proves that the regeneration term is not bookkeeping decoration. It can genuinely finance Recovery behavior that the initial potential alone cannot support.

## Boundary

Gate 34 does **not** imply eventual stabilization when regeneration is unbounded. An update system that creates fresh resource indefinitely may fund indefinitely many Recovery flips.

Stabilization can be recovered only after adding a global bound on total regeneration, or a stronger structural condition showing that resource creation itself eventually ceases.

This is the bridge toward later work on growing ontologies and product updates, where new epistemic coordinates may be generated dynamically.
