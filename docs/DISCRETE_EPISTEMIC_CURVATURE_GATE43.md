# Gate 43: Discrete Epistemic Curvature

## Research question

Gate 42 showed that one closed evidence-control loop can return to the same syntactic control label and Recovery status while leaving a nonzero displacement in full epistemic model space. Gate 43 asks the stronger compositional question:

> Can two anchored evidence loops fail to commute?

We compare the same two excursions `P` and `Q`, with a return to one syntactic anchor `A` after each excursion:

```text
A -> P -> A -> Q -> A
A -> Q -> A -> P -> A
```

A difference between the two final `Model` states is called a **discrete epistemic curvature witness** or **nonzero epistemic loop commutator**.

## Formal object

`EpistemicLoopCommutator start A P Q` stores the two endpoints and admissible Conditionalization runs for schedules `[P,A,Q,A]` and `[Q,A,P,A]`. Its `Noncommuting` predicate is simply endpoint inequality. `DiscreteEpistemicCurvatureAt` asserts existence of such a noncommuting commutator.

Gate 39 supplies an important control theorem: each fixed schedule has a unique endpoint. Therefore endpoint divergence between the two orders is not nondeterminism and does not require a hidden history register.

## Concrete witness

The witness reuses the three-world DynamicInstability model.

- neutral anchor `A`: the classically valid formula `p ∨ ¬p` in this concrete model;
- excursion `P`: belief-dependent evidence `B p`;
- excursion `Q`: atomic evidence `e`.

Because the valuation of `p` is classical at all three worlds and Conditionalization changes only probabilities, the anchor remains a full positive-extension return point throughout the witness.

The two loop compositions are:

```text
A -> Bp -> A -> e  -> A
A -> e  -> A -> Bp -> A
```

The first endpoint has belief profile

```text
B p = T / N / T
```

while the reversed composition has

```text
B p = T / T / T.
```

Thus they already disagree on the modal observation `B p` at world `b`, so the full endpoint models are unequal.

## Interpretation

This strengthens Gate 42. A single loop can transport epistemic state, and now two loops can compose noncommutatively. The finite update space therefore supports an order-sensitive loop algebra.

The mechanism remains the semantic feedback isolated in Gates 36 and 40: atomic evidence changes the probability model, which changes the positive extension of later belief-dependent evidence. The two loop orders consequently do not denote the same sequence of extensional conditioning events.

## No-overclaim boundary

The word *curvature* is used in a discrete structural sense only. Gate 43 does **not** construct or verify:

- a differentiable manifold,
- a connection,
- parallel transport in the differential-geometric sense,
- a curvature tensor,
- a holonomy group.

The verified claim is narrower:

> There exist two finite anchored Conditionalization loops built from the same syntactic ingredients whose opposite compositions have different epistemic endpoints, while each fixed order is deterministic.

That is enough to justify the terms **discrete epistemic curvature witness** and **nonzero epistemic loop commutator**, but not an identification with differential geometry.
