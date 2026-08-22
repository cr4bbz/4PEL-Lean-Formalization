# Threshold-Side Robustness under Conditionalization

Status: **active build gate** on `research/preface-case-study`.

Do not mark the new robustness theorems compiler-verified until a fresh local
`lake build` has passed with `PEL4/ModalDynamicsRobustness.lean` imported.

## Motivation

The verified dynamic picture now has two striking facts:

```text
probability-free formulas are invariant under probability-only update;
K(B p) can nevertheless realize every T/F/B/N -> T/F/B/N transition.
```

The missing question is what lies between those extremes. A formula may contain
`bel` and still remain dynamically invariant. The relevant boundary should not
be purely syntactic.

## Threshold support masses

For a modal formula `phi`, agent `i`, and world `w`, define the positive and
negative support masses used by probabilistic belief:

```text
M+(m,i,w,phi)
M-(m,i,w,phi).
```

The belief value is exactly the pair of Lockean threshold decisions:

```text
B_i(phi) =
  ( [M+ >= c_i], [M- >= c_i] ).
```

Hence between arbitrary before/after models:

```text
B_i(phi)_after = B_i(phi)_before
iff
positive threshold bit is unchanged
and
negative threshold bit is unchanged.
```

This is the proposed exact pointwise **Threshold-Side Robustness** boundary.

## Compositional robustness

`ModalConditionalizationRobust` lifts the pointwise idea through the modal
language.

```text
prop        robust
not phi     robust if phi robust
phi and psi robust if both robust
K phi       robust if phi robust
Diamond phi robust if phi robust
B_i phi     robust if its two threshold bits are unchanged at every world
```

The `bel` clause intentionally does **not** require the embedded `phi` itself to
be robust. Internal semantic or probabilistic movement may be absorbed as long
as neither final threshold bit flips.

The target theorem is:

```text
ModalConditionalizationRobust m E phi
->
evalModal (conditionalize m E) w phi = evalModal m w phi.
```

## Strict extension beyond the probability-free fragment

The verified complete-reachability family supplies a natural diagonal test.
Set

```text
source = target = v.
```

Conditioning still replaces the uniform prior by a posterior concentrated on the
focus world, so the probability distribution changes substantially. Yet the
belief state remains `v` before and after at every world.

Thus `B p` should be robust even though it is syntactically not
`ModalProbabilityFree`. Consequently `K(B p)` should also be invariant.

If the build passes, this proves that the older probability-free theorem is a
proper syntactic safe zone inside a larger semantic robustness region.

## Philosophical interpretation

Complete dynamic reachability and threshold-side robustness are complementary:

```text
cross a threshold side -> categorical epistemic change is possible;
remain on both sides    -> categorical belief status is protected.
```

The invariant is therefore not raw probability. It is the ordered pair of
threshold regions occupied by positive and negative support.

This gives the dynamic 4-PEL state space a cell-like geometry: probability may
move continuously inside a threshold cell without changing the four-valued
status, while crossing one of its walls changes one coordinate of the epistemic
state.

## Novelty boundary

No novelty claim is made. The result should later be compared with robustness
and sensitivity results for Lockean belief, probabilistic belief revision,
threshold classifiers, and four-valued dynamic epistemic systems.
