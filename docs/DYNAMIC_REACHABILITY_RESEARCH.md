# Complete Dynamic Epistemic Reachability

Status: **VERIFIED** on `research/complex-coordinates` with Lean 4.31.

The imported `PEL4/ModalDynamicsReachability.lean` gate has passed a fresh local
`lake build` after the free-variable proof repair. The generic reachability
result and its concrete glut/gap consequences are therefore compiler-verified.

## Question

Given the four complete FDE values

```text
T  F  B  N
```

which ordered transitions can admissible probabilistic conditionalization
realize at the level of evidence-stable knowledge of a probabilistic belief,

```text
K(B p) ?
```

The update is required to leave accessibility, atomic valuation, and the
Lockean threshold fixed. Only the probability measure may change.

## Six-world construction

For arbitrary source and target FDE values, use six mutually accessible worlds:

```text
focus, a1, a2, a3, a4, spare.
```

The atomic valuation of `p` is fixed across the update:

```text
p(focus) = target
p(a1) = p(a2) = p(a3) = p(a4) = source
p(spare) = N.
```

The prior is uniform and the threshold is `2/3`.

A second atom `e` is positive only at `focus`. Conditioning on `e` therefore
moves the entire posterior probability mass to `focus` while leaving the model's
relation and valuation unchanged.

## Why the source survives the prior

The four source anchors contribute `4/6 = 2/3` of the prior mass.

For `source = T`, positive support reaches threshold while negative support can
receive at most the single `focus` contribution, so the prior belief remains T.

For `source = F`, the dual argument gives F.

For `source = B`, both support channels already reach threshold on the four
anchors, so the prior remains B independently of the target.

For `source = N`, the four anchors and spare world contribute no support; the
single focus world contributes at most `1/6` to either channel, so both remain
below threshold and the prior is N.

Hence

```text
B(p) before = source.
```

Because the local probability measure is source-world independent, the B(p)
profile is homogeneous throughout the accessibility range. Evidence-stable
knowledge therefore has the same value:

```text
K(B p) before = source.
```

## Why the posterior equals the target

After conditioning on `e`, posterior mass is one on `focus` and zero elsewhere.
Therefore threshold belief reproduces the complete FDE value carried by
`focus`:

```text
B(p) after = target.
```

Again the profile is homogeneous across source worlds, so

```text
K(B p) after = target.
```

The verified generic theorem is therefore

```text
for every source target : FDEValue,
  K(B p) before = source
  and
  K(B p) after = target.
```

Since an `FDEValue` has two Boolean coordinates, this covers all sixteen
ordered transitions:

```text
        target
        T   F   B   N
      +---------------
T     | x   x   x   x
F     | x   x   x   x
B     | x   x   x   x
N     | x   x   x   x
^
source
```

## Verified consequences

1. **Dynamic reachability:** the K(Bp) reachability graph over T/F/B/N is
   complete at the level of the semantics. No ordered pair is forbidden in
   principle by admissible conditionalization.
2. **Dynamic gluts and gaps:** conditionalization can create and remove both
   knowledge-level B and N states while keeping R, atomic valuation, and the
   Lockean threshold fixed.

This does **not** claim that every fixed concrete model can realize every
transition. It is an existential model-family result: for each ordered pair
there exists a six-world member of the family realizing that transition.

Working name: **Complete Dynamic Epistemic Reachability**.

## Novelty boundary

No novelty claim is made here. The construction should later be compared with
four-valued dynamic epistemic logics, probabilistic belief revision, and
bilattice-valued dynamic systems. The current claim is the internal
compiler-verified result only.
