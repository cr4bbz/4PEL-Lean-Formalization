# Universal Latent-Conflict Topology

## Status

This note generalizes the three-claim Latent-Conflict Triangle from
`PREFACE_SHARPNESS.md` to arbitrary finite arity and identifies the higher-
dimensional object of which the triangle is only a coarse projection.

The Lean module

```text
PEL4/Paradoxes/PrefaceConflictTopologyN.lean
```

proves the denominator-free n-claim bounds.

## 1. Raw n-claim geometry

Let

```text
B_i = { worlds where p_i has object-level value B }
```

inside a sharp local conflict carrier

```text
L = union_i B_i.
```

Write

```text
d   = P(L)
b_i = P(B_i)
S   = sum_i b_i
p   = max_i b_i
n   = number of claims.
```

Then the elementary union and maximum bounds give

```text
d <= S <= n*p <= n*d.
```

`PrefaceConflictTopologyN.lean` formalizes exactly this chain for arbitrary
finite lists of local glut masses.

Two immediate consequences are:

```text
d <= n*p
```

so at least one conjunct carries at least a `1/n` share of the carrier mass,
and

```text
S <= n*d
```

so total local glut multiplicity can never exceed `n` complete copies of the
carrier.

The module also proves:

```text
n*p = d  ->  S = d.
```

Thus exact minimum concentration automatically eliminates redundancy.  The
lower-left corner of the normalized geometry is structurally forced rather
than chosen by convention.

## 2. Dimension-free normalization

Assume `n >= 2` and `d > 0`.  Define

```text
kappa = p/d
rho   = S/d.
```

Then

```text
1/n <= kappa <= 1
1   <= rho   <= n*kappa.
```

Normalize these to `[0,1]`:

```text
q = (n*kappa - 1)/(n-1)
r = (rho - 1)/(n-1).
```

Equivalently,

```text
q = (n*p - d)/((n-1)d)
r = (S - d)/((n-1)d).
```

The raw chain becomes

```text
0 <= r <= q <= 1.
```

Therefore every finite arity projects into the same standard 2-simplex:

```text
T_conflict = { (q,r) in [0,1]^2 : r <= q }.
```

This gives an arity-independent geometric summary of latent conflict.

### Interpretation

`q` is **concentration**.  In conditional form,

```text
kappa = max_i P(B_i | L)
q = (n*kappa - 1)/(n-1).
```

`r` is **redundancy**.  If `K(w)` is the number of conjuncts that are B at a
carrier world `w`, then

```text
rho = E[K | L]
r = (E[K | L] - 1)/(n-1).
```

So the coordinates have direct probabilistic meanings rather than being merely
geometric rescalings.

## 3. Boundary semantics

### Bottom edge: `r = 0`

Here

```text
S = d.
```

The union bound is exact, so local conflict carriers are non-redundant up to
measure zero.  Conflict is distributed as a partition of the carrier.

`q` then records how unevenly that partition is distributed among claims.

### Right edge: `q = 1`

Here

```text
p = d.
```

At least one proposition is glutty throughout the entire carrier region.
Redundancy may still range from minimal to maximal.

### Diagonal: `r = q`

Here

```text
S = n*p.
```

Every local glut mass reaches the common peak.  Marginal conflict loads are
equal, although their higher-order overlaps can still differ.

### Vertices

```text
(0,0) : maximally distributed, non-redundant
(1,0) : maximally concentrated, non-redundant
(1,1) : maximally redundant.
```

The three-claim witnesses from `PrefaceSharpness.lean` and
`PrefaceConflictTopologyN.lean` realize these corners.

## 4. The triangle is only a projection

The pair `(q,r)` does not determine the full local conflict structure.

At every carrier world define the **conflict incidence pattern**

```text
S(w) = { i : p_i = B at w }.
```

Sharpness guarantees that `S(w)` is nonempty on the entire carrier.
For each nonempty subset `A` of `{1,...,n}`, define

```text
x_A = P(S(w) = A | w in L).
```

There are `2^n - 1` nonempty patterns and

```text
x_A >= 0
sum_{A != empty} x_A = 1.
```

Hence the complete conditional incidence distribution lies in the standard
simplex

```text
Delta^(2^n - 2).
```

We call this the **Conflict Incidence Simplex**.

The local glut marginals are linear projections:

```text
b_i/d = sum_{A contains i} x_A.
```

The redundancy statistic is also linear:

```text
rho = sum_A |A| * x_A = E[|S(w)| | L].
```

Concentration is obtained from the maximum marginal:

```text
kappa = max_i sum_{A contains i} x_A.
```

Thus the Latent-Conflict Triangle is a two-dimensional summary projection of a
much higher-dimensional incidence simplex.

For `n = 3`, the full object is already

```text
Delta^6
```

because the seven nonempty conflict patterns are

```text
{1}, {2}, {3}, {1,2}, {1,3}, {2,3}, {1,2,3}.
```

The familiar triangle therefore discards substantial higher-order overlap
information even in the smallest philosophically interesting case.

## 5. Exactness of the triangular image

At the level of measurable conflict-carrier events, the inequalities are not
only necessary.  They are sufficient.

Given any

```text
0 <= r <= q <= 1
```

set

```text
kappa = (1 + (n-1)q)/n
rho   = 1 + (n-1)r.
```

Then

```text
1/n <= kappa <= 1
1 <= rho <= n*kappa.
```

A carrier can first be partitioned into `n` non-redundant pieces with maximum
piece size `kappa`.  This realizes total multiplicity `rho = 1`.  Additional
memberships can then be added inside the already covered carrier, using the
remaining marginal capacity up to `kappa`, until the desired total
multiplicity `rho` is reached.  Because

```text
rho - 1 <= n*kappa - 1,
```

exactly enough capacity is available.

Therefore the continuous feasible image is the whole triangle, not merely a
subset of it.

A fully constructive Lean realization theorem for finite rational points is a
next target; the current Lean file proves the necessary raw inequalities.

## 6. Coupling to sharp Preface conflict

For a sharp global conjunction glut at Lockean threshold `c`, the previous
results give

```text
d = 2c - 1.
```

Therefore the topology coordinates reconstruct two useful local statistics:

```text
peak local glut mass
  = (2c-1) * (1 + (n-1)q)/n
```

and

```text
summed local glut mass
  = (2c-1) * (1 + (n-1)r).
```

So `c`, `q`, and `r` separate three conceptually different quantities:

```text
c : epistemic strictness / required carrier mass
q : concentration of latent conflict
r : redundancy of latent conflict.
```

For fixed `n`, sharp signed Preface states therefore have a natural coarse
parameter space

```text
(1/2,1) x Delta^2,
```

with the first factor tracing the Sharp Conflict Spine and the second factor
recording the normalized latent-conflict topology.

Provisionally, this product geometry can be called the **Sharp Conflict Prism**.

## 7. Local-T feasibility

For every strict threshold

```text
1/2 < c < 1,
```

the full topology triangle remains compatible with all local threshold beliefs
being `T`.

The reason is that every local glut mass satisfies

```text
b_i <= d = 2c-1 < c.
```

Thus the B-region alone never makes a local belief glutty.  The remaining joint
F-region has mass `1-c`; its required local falsity can be distributed among
conjuncts while staying below each remaining negative-evidence capacity.

The endpoint `c = 1` is degenerate: `d = 1`, so points with `q = 1` force some
local glut mass to equal the threshold and therefore cease to have local belief
state `T`.

A formal model-construction theorem for this feasibility claim remains open.

## 8. Philosophical consequence

The signed Preface programme now separates at least four descriptive levels:

```text
local threshold-belief profile
        |
        v
global FDE macrostate
        |
        v
carrier mass and (q,r) topology
        |
        v
full conflict incidence simplex.
```

Each projection loses information.

In particular, two agents can agree on every local threshold belief, the global
FDE state, the exact sharp carrier mass, and even the same `(q,r)` coordinates,
while differing in pairwise and higher-order conflict incidence patterns.

Thus epistemic conflict has a genuine internal combinatorial geometry that is
not recoverable from ordinary belief-set descriptions.

## Next targets

1. Prove finite-rational realization of every lattice point in the triangle.
2. Formalize the Conflict Incidence Simplex using nonempty finite subsets.
3. Express `q` and `r` as projections of incidence coordinates.
4. Characterize fibers: which distinct incidence distributions share one
   `(q,r)` point?
5. Test whether independence, exchangeability, or symmetry restrictions collapse
   these fibers.
6. Transfer the incidence geometry to Lottery, Moore, and Contrary-to-Duty
   case studies.
