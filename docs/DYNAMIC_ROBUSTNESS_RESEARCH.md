# Threshold-Side Robustness under Conditionalization

Status: **VERIFIED** on `research/preface-case-study` by local Lean 4.31 `lake build` reported 2026-08-22.

## Motivation

The verified dynamic picture has two striking facts:

```text
probability-free formulas are invariant under probability-only update;
K(B p) can nevertheless realize every T/F/B/N -> T/F/B/N transition.
```

Threshold-Side Robustness identifies the semantic boundary between those extremes. A formula may contain `bel` and still remain dynamically invariant. The relevant boundary is not purely syntactic.

## Threshold support masses

For a modal formula `phi`, agent `i`, and world `w`, define the positive and negative support masses used by probabilistic belief:

```text
M+(m,i,w,phi)
M-(m,i,w,phi).
```

The belief value is exactly the pair of Lockean threshold decisions:

```text
B_i(phi) =
  ( [M+ >= c_i], [M- >= c_i] ).
```

Lean verifies the exact pointwise boundary:

```text
B_i(phi)_after = B_i(phi)_before
iff
positive threshold bit is unchanged
and
negative threshold bit is unchanged.
```

This is the formal core of **Threshold-Side Robustness**.

## Compositional robustness

`ModalConditionalizationRobust` lifts the pointwise idea through the modal language.

```text
prop        robust
not phi     robust if phi robust
phi and psi robust if both robust
K phi       robust if phi robust
Diamond phi robust if phi robust
B_i phi     robust if its two threshold bits are unchanged at every world
```

The `bel` clause intentionally does **not** require the embedded `phi` itself to be robust. Internal semantic or probabilistic movement may be absorbed as long as neither final threshold bit flips.

Lean verifies:

```text
ModalConditionalizationRobust m E phi
->
evalModal (conditionalize m E) w phi = evalModal m w phi.
```

## Strict extension beyond the probability-free fragment

The complete-reachability family supplies a diagonal witness. Set

```text
source = target = v.
```

Conditioning replaces the uniform prior by a posterior concentrated on the focus world, so the probability distribution changes substantially. Yet `B p` remains `v` before and after at every world.

Lean verifies that this `B p` is robust while also proving that it is not `ModalProbabilityFree`. Consequently `K(B p)` is invariant under the same nontrivial update.

Thus the older probability-free theorem is a strict syntactic safe zone inside a larger semantic robustness region.

## Philosophical interpretation

Complete dynamic reachability and threshold-side robustness are complementary:

```text
cross a threshold side -> categorical epistemic change is possible;
remain on both sides    -> categorical belief status is protected.
```

The invariant is therefore not raw probability. It is the ordered pair of threshold regions occupied by positive and negative support.

This gives the dynamic 4-PEL state space a cell-like geometry: probability may move inside a threshold cell without changing the four-valued status, while changing one of the two threshold bits moves the categorical state to another cell.

The next build gate, `PEL4/ModalDynamicsGeometry.lean`, formalizes the induced Boolean-square geometry of the four categorical states. Continuous path/wall-crossing claims are deliberately postponed until a suitable topological or ordered path layer exists.

## Novelty boundary

No novelty claim is made. The result should later be compared with robustness and sensitivity results for Lockean belief, probabilistic belief revision, threshold classifiers, and four-valued dynamic epistemic systems.
