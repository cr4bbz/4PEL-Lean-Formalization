# Gate 35 — Growing Ontology / Product Update

## Research question

Gate 34 introduced regenerative Recovery budgets: finite Recovery resource may be created along a trajectory, provided every created unit is explicitly charged. The open question was whether 4PEL already contains a concrete structural mechanism that can motivate such regeneration.

Product Update is the natural test. It replaces a world space `W` by a filtered world-event product `W × Act`. Learning can therefore change not only probabilities over a fixed ontology but also the number of represented epistemic states.

Gate 35 asks:

> How much can one Product Update enlarge the represented state space, and how can that finite enlargement constrain a regenerative Recovery budget?

## Product-state capacity

For a model `m` and action model `a`, define

```text
productWorldCount(m,a)    = number of surviving filtered world-event pairs
productWorldCapacity(m,a) = |W| * |Act|
```

The exact list-product theorem and a filter monotonicity theorem yield

```text
productWorldCount(m,a) <= productWorldCapacity(m,a).
```

Thus 4PEL Product Update has an explicit finite geometric envelope:

\[
\boxed{|W'| \le |W|\,|E|.}
\]

This result uses only the world/event product and precondition filter. It does not depend on the current prototype axioms for `product_mu`.

## Ontology growth

Gate 35 defines the net one-step ontology growth

```text
productOntologyGrowth(m,a)
  = productWorldCount(m,a) - |W|.
```

Natural subtraction records zero when the update contracts rather than expands the represented ontology.

The general capacity theorem implies

\[
\Delta_{\mathrm{ont}}(m,a) \le |W|\,|E|.
\]

For the sharp minimal expansion schema, assume one prior world, two events, and that both world-event pairs survive the precondition filter. Then

\[
|W|=1,\qquad |E|=2,\qquad |W'|=2,
\]

and therefore

\[
\boxed{\Delta_{\mathrm{ont}}=1.}
\]

The theorem is `productOntologyGrowth_eq_one_of_singleton_twoEvents`.

## Bridge to regenerative Recovery budgets

Gate 35 deliberately does **not** define ontology growth to be Recovery resource. That would be too strong: adding represented states need not automatically make a Recovery flip possible.

Instead it introduces an explicit funding condition:

```text
ProductGrowthFundsRecoveryPath
```

meaning that total Gate-34 regeneration along a Recovery path does not exceed the Product-Update ontology-growth budget.

Under this condition, the Gate-34 accounting theorem gives

\[
\boxed{
\#\mathrm{RecoveryChanges}
\le
\Phi_0 + \Delta_{\mathrm{ont}}
}
\]

via `recoveryRegenerative_changeCount_le_initial_add_productGrowth`.

A coarser theorem replaces net growth by the raw Cartesian capacity:

\[
\#\mathrm{RecoveryChanges}
\le
\Phi_0 + |W|\,|E|.
\]

The important point is conceptual: ontology growth now supplies a **concrete finite upper envelope** that can fund an otherwise abstract regenerative budget, while the bridge remains a separately stated semantic assumption.

## Sharp compatibility witness

A two-state regenerative Recovery system starts with potential zero and performs one Recovery-status change. The edge regenerates exactly one unit.

For the one-world/two-event Product-Update schema above, Gate 35 proves

```text
regeneration total = ontology growth = Recovery change count = 1.
```

Hence the bound is sharp:

\[
1 = 0 + 1.
\]

This demonstrates compatibility between Product-Update ontology growth and Gate-34 regeneration without identifying the two notions by definition.

## Repeated expansion warning

Gate 35 also records the erased cardinality envelope

```text
iteratedProductCapacity 1 [2,2,2] = 8.
```

This is not yet a theorem about heterogeneous repeated 4PEL Product Updates. It highlights the next structural issue: repeated Product Updates change the world type at each stage (`W`, `W×E₁`, `(W×E₁)×E₂`, ...), and raw capacity can grow multiplicatively.

So an initial-potential-only Recovery theorem cannot simply be carried over to indefinitely growing ontologies. A cumulative growth or regeneration control is required.

## No-overclaim boundary

Gate 35 does not prove:

- that every new Product-Update state contributes one unit of Recovery resource;
- that ontology growth is sufficient for a Recovery flip;
- that repeated Product Updates always grow rather than shrink the state space;
- that the prototype `product_mu` already supplies a fully verified Bayesian Product Update;
- that unbounded ontology growth is compatible with eventual Recovery stabilization.

What is proved is the finite geometric envelope and the conditional bridge from that envelope to the already verified Gate-34 Recovery accounting theory.

## Next research step

With the growing-ontology issue exposed, the next roadmap item is naturally the hysteresis-loop / controlled-dynamics program. In particular, Gate 42 can ask whether a closed cycle of epistemic updates leaves a nonzero displacement in the full 4PEL state, before Gate 43 recasts Gate-39 state sufficiency as an explicit controlled Markov-style transition system.
