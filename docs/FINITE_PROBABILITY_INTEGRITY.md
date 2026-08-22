# Finite Probability Integrity

Status: **VERIFIED**

## Motivation

The legacy 4-PEL `Model` deliberately uses a lightweight finite probability interface:

```text
mu : Ag -> W -> FiniteSet W -> Rat
mu_total : mu(R) = 1
mu_empty : mu([]) = 0
```

This has been sufficient for the existing finite theorem laboratory. It is not yet strong enough, however, for a publication-level claim that an affine support trajectory is a trajectory of genuine probability models. In particular, the legacy type does not itself package nonnegativity, extensionality, monotonicity, or finite additivity.

## Verified compatibility layer

`PEL4/FiniteProbabilityIntegrity.lean` introduces a separate stronger contract rather than modifying `Model` globally.

For one local measure `mu` on accessible support `R`, `FiniteProbabilityIntegrity mu R` records:

```text
R is duplicate-free
accessible event masses are nonnegative
set-extensionally equal events have equal mass
inclusion implies monotonicity
disjoint events are finitely additive
mu([]) = 0
mu(R) = 1
```

`ModelProbabilityIntegrity m` requires this at every agent/world pair.

`StrongProbabilityModel` wraps an ordinary legacy `Model` together with a proof of `ModelProbabilityIntegrity`.

A fresh local Lean 4.31 `lake build` has compiled this module through the root `PEL4.lean` import.

## Why this is deliberately separate

The repository already contains many finite concrete models. Changing the fields of `Model` directly would turn a foundational audit into a large mechanical refactor and, more importantly, would blur a scientifically meaningful question:

```text
which existing witnesses actually satisfy the stronger probability laws?
```

Promotion to the stronger layer is therefore an explicit theorem obligation. No pre-existing witness is automatically promoted merely because the compatibility layer itself compiles.

## Next gates

The next sequence is:

1. construct finite probability measures from nonnegative rational world weights;
2. prove the integrity laws generically for the weight-generated constructor;
3. promote the dynamic reachability family through that constructor or an equivalent integrity proof;
4. prove convex rational interpolation preserves finite probability integrity;
5. lift affine support crossings to genuine intermediate model states.

Only after those steps should the project claim a model-level epistemic trajectory rather than a support-mass interpolation.
