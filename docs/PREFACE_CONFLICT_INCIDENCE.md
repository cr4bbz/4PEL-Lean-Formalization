# Conflict Incidence Simplex

## Purpose

The Latent-Conflict Triangle records only two normalized statistics of a sharp
signed Preface conflict:

```text
q : concentration
r : redundancy.
```

Those coordinates are useful but coarse.  They do not determine how local
object-level gluts co-occur across propositions.

This note introduces the next descriptive layer: the **Conflict Incidence
Simplex**.

## Three-claim case

For three claims, every world in the local conflict carrier has one of seven
nonempty local-glut patterns:

```text
{1}
{2}
{3}
{1,2}
{1,3}
{2,3}
{1,2,3}.
```

Let their finite masses be

```text
x1, x2, x3, x12, x13, x23, x123.
```

With carrier mass `d`, they satisfy

```text
x1 + x2 + x3 + x12 + x13 + x23 + x123 = d.
```

After normalization by `d`, this is the standard simplex

```text
Delta^6.
```

`PEL4/Paradoxes/PrefaceConflictIncidence3.lean` formalizes this finite-count
version.

## Marginal projection

The local glut marginals are linear projections of the incidence coordinates:

```text
b1 = x1 + x12 + x13 + x123
b2 = x2 + x12 + x23 + x123
b3 = x3 + x13 + x23 + x123.
```

The total local multiplicity is therefore

```text
S = b1 + b2 + b3
  = x1 + x2 + x3
  + 2(x12 + x13 + x23)
  + 3x123.
```

Lean proves this as

```text
totalLocal_incidence_identity.
```

Using the carrier normalization, this becomes the exact redundancy identity

```text
S = d + x12 + x13 + x23 + 2x123.
```

Thus redundancy is not an opaque scalar.  It counts higher-order incidence:

* pair-only conflict contributes one extra membership,
* triple conflict contributes two extra memberships.

Lean proves this as

```text
redundancy_incidence_decomposition.
```

## Triangle boundaries as simplex faces

The coarse Latent-Conflict Triangle now receives a direct incidence
interpretation.

### Bottom edge: `r = 0`

Here `S = d`.  The decomposition above forces

```text
x12 = x13 = x23 = x123 = 0.
```

So exact absence of redundancy is precisely the singleton face of `Delta^6`.
No carrier world contains more than one local glut.

Lean:

```text
no_redundancy_iff_singleton_face.
```

### Right edge: full concentration

If proposition 1 fills the whole carrier,

```text
b1 = d,
```

then every incidence pattern omitting proposition 1 must vanish:

```text
x2 = x3 = x23 = 0.
```

Lean:

```text
b1_full_carrier_iff_no_pattern_without_1.
```

The analogous claims follow by permutation for propositions 2 and 3.

### Maximum redundancy

If

```text
S = 3d,
```

then every carrier membership slot is saturated.  The profile collapses to the
single triple-conflict vertex:

```text
x123 = d
```

and every other incidence coordinate is zero.

Lean:

```text
maximal_redundancy_forces_triple_vertex.
```

## A nontrivial fiber

The key philosophical question is whether the coarse projection loses genuine
structure.  It does.

The module contains two profiles with carrier mass

```text
d = 6
```

and identical local marginals

```text
(b1,b2,b3) = (3,3,3).
```

Therefore both have

```text
S = 9
p = 3
q = r = 1/4.
```

But the underlying incidence distributions differ.

### Fiber A

```text
x12 = 3
x3  = 3
```

all other coordinates zero.

This profile has only pair conflict plus a singleton block and no triple
conflict.

### Fiber B

```text
x1   = 1
x2   = 1
x3   = 2
x12  = 1
x123 = 1.
```

This profile contains singleton, pair, and genuine triple conflict.

Lean proves that the two profiles agree on carrier, every local marginal, total
multiplicity, and peak:

```text
fiber_same_coarse_projection.
```

It also proves that their higher-order overlap and triple mass differ:

```text
fiber_hidden_structure_differs.
```

Hence the fiber over one coarse topology point is nontrivial even after fixing
more information than `(q,r)` alone.

## Philosophical consequence

The signed Preface hierarchy is now:

```text
local threshold-belief profile
        |
        v
global FDE macrostate
        |
        v
sharp carrier mass
        |
        v
(q,r) conflict topology
        |
        v
local glut marginals
        |
        v
full conflict incidence profile.
```

Every downward refinement can distinguish states identified by the level above.

The new result is especially strong because the two fiber witnesses have the
same local glut marginals.  Thus even knowing the proposition-by-proposition
amount of contradiction is not enough to reconstruct how contradictions
co-occur.

A useful provisional principle is:

> **Incidence Underdetermination:** marginal conflict loads do not determine the
> higher-order organization of epistemic conflict.

This is analogous to the familiar fact that one-dimensional marginals do not
determine a joint probability distribution, but here the joint object records
which propositions are simultaneously glutty rather than which ordinary events
co-occur.

## General n-claim object

For `n` claims, let

```text
x_A = P(S(w) = A | w in L)
```

for each nonempty subset

```text
A subseteq {1,...,n}.
```

There are `2^n - 1` coordinates and one normalization equation, so the full
conditional incidence object is

```text
Delta^(2^n - 2).
```

The local marginals are

```text
b_i/d = sum_{A contains i} x_A,
```

and normalized redundancy is the projection

```text
r = (E[|A|] - 1)/(n-1).
```

Concentration is obtained from the largest marginal.

## Next formal targets

1. Define arbitrary finite incidence patterns in Lean rather than enumerating
   the seven three-claim coordinates.
2. Prove the general multiplicity identity

   ```text
   sum_i b_i = sum_A |A| * x_A.
   ```

3. Prove the general redundancy decomposition

   ```text
   sum_i b_i - d = sum_A (|A|-1) * x_A.
   ```

4. Characterize the `r = 0` face as support only on singleton patterns.
5. Characterize maximal redundancy as support only on the full-set pattern.
6. Study fibers with fixed marginals as transportation / contingency polytopes.
7. Determine which additional assumptions, such as exchangeability or
   independence, shrink these fibers.
