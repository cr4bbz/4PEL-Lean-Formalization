# Fixed-Marginal Conflict Fibers

## Motivation

The Conflict Incidence Simplex records the full distribution of nonempty local
object-level glut patterns.  For `n` claims its normalized coordinates are
indexed by the `2^n - 1` nonempty subsets of `{1,...,n}`.

The local glut marginals are linear projections of that simplex.  This raises a
natural question:

> How much higher-order conflict structure remains after every local glut
> marginal has been fixed?

The answer is already nontrivial for three claims and grows exponentially with
arity.

## Generic affine dimension

Let

```text
x_A >= 0
```

for every nonempty subset `A` of `{1,...,n}` and impose

```text
sum_A x_A = 1
```

plus fixed marginal equations

```text
sum_{A contains i} x_A = m_i
```

for `i = 1,...,n`.

There are

```text
2^n - 1
```

incidence variables.  For `n >= 2`, the normalization row and the `n` marginal
rows are linearly independent: singleton patterns force every marginal-row
coefficient to be the negative of the normalization coefficient, and any pair
pattern then forces that common coefficient to vanish.

Therefore, whenever the chosen marginal vector lies in a region where the
intersection has full relative dimension, the fixed-marginal affine fiber has
generic dimension

```text
(2^n - 1) - (n + 1)
  = 2^n - n - 2.
```

Examples:

```text
n = 2  -> 0 hidden affine dimensions
n = 3  -> 3
n = 4  -> 10
n = 5  -> 25
n = 10 -> 1012.
```

Thus proposition-by-proposition conflict marginals suppress an exponentially
growing amount of higher-order incidence information.

This is a dimensional statement about the unconstrained affine intersection.
Specific boundary marginals can collapse the realized polytope to lower
dimension.

## The symmetric three-claim mid-fiber

`PEL4/Paradoxes/PrefaceConflictFiber3.lean` studies the coarse data

```text
b1 = b2 = b3 = m
d = 2m.
```

Then

```text
S = 3m
p = m
```

and hence

```text
kappa = p/d = 1/2
rho   = S/d = 3/2
q = r = 1/4.
```

So an entire higher-dimensional family lies over one fixed point of the
Latent-Conflict Triangle.

### Necessary overlap equation

Every incidence profile in this fiber satisfies

```text
x12 + x13 + x23 + 2*x123 = m.
```

Moreover its singleton coordinates are forced:

```text
x1 = x23 + x123
x2 = x13 + x123
x3 = x12 + x123.
```

Lean proves these equations as

```text
symmetric_mid_fiber_equations.
```

Hence four overlap coordinates contain all remaining information, subject to
one linear equation: three degrees of freedom, exactly matching the generic
fixed-marginal dimension for `n = 3`.

## Constructive converse

The Lean definition

```text
symmetricMidFiberFromOverlap
```

starts with arbitrary nonnegative finite counts satisfying

```text
x12 + x13 + x23 + 2*x123 = m
```

and constructs

```text
x1 = x23 + x123
x2 = x13 + x123
x3 = x12 + x123
```

with carrier

```text
d = 2m.
```

Lean then proves that every such construction has exactly the fixed projection

```text
b1 = b2 = b3 = m
S = 3m
p = m.
```

The relevant theorems are

```text
symmetricMidFiberFromOverlap_projection
symmetricMidFiberFromOverlap_coarse.
```

Thus the overlap equation is sufficient as well as necessary at the finite
count level.

## Tetrahedral geometry

Introduce the weighted overlap coordinate

```text
y123 = 2*x123.
```

The fiber equation becomes

```text
x12 + x13 + x23 + y123 = m.
```

After division by `m`:

```text
u12 + u13 + u23 + u123 = 1
u12,u13,u23,u123 >= 0.
```

Therefore the continuous normalized fiber is the standard tetrahedron

```text
Delta^3.
```

The integer finite-count representation samples a lattice inside this
tetrahedron, with the fourth weighted coordinate constrained by the parity of
`2*x123`.  Increasing the common scale refines that lattice.

### Existing witnesses inside the tetrahedron

The earlier profiles are now located geometrically.

Fiber A:

```text
(x12,x13,x23,2*x123) = (3,0,0,0).
```

It is a pair-conflict vertex.

Fiber B:

```text
(x12,x13,x23,2*x123) = (1,0,0,2).
```

It lies on the edge connecting that pair direction to the triple-conflict
direction.

Both still project to

```text
q = r = 1/4
```

and the same full local marginal vector.

## Philosophical interpretation

The fixed-marginal fiber makes the information loss precise.

Knowing

```text
P_B(p1), ..., P_B(pn)
```

specifies how much conflict each proposition carries individually.  It does not
specify whether those conflicts occur in the same epistemic possibilities.

The hidden dimensions encode forms of **conflict correlation**:

```text
pair co-conflict
triple co-conflict
...
n-way co-conflict.
```

This suggests a distinction between

```text
marginal conflict load
```

and

```text
interaction structure of conflict.
```

A provisional principle is:

> **Conflict Interaction Underdetermination:** even a complete vector of local
> contradiction probabilities leaves higher-order simultaneous contradiction
> structure underdetermined.

For large `n`, the dimensional gap is exponential.  Ordinary belief-set or
marginal descriptions therefore retain only a very small shadow of the full
signed-evidence organization.

## Next direction: interaction coordinates

Incidence coordinates `x_A` are direct and geometrically transparent, but they
are not the only useful basis.

A natural next step is to derive interaction coordinates over the Boolean
lattice of claim subsets, separating

```text
first-order marginal conflict
pairwise excess co-conflict
triple excess co-conflict
...
```

This is structurally related to Möbius / inclusion-exclusion transforms on
subset lattices.  Such a basis could make the hidden fiber dimensions
interpretable as distinct orders of epistemic conflict interaction rather than
merely as free simplex coordinates.

## Formal next targets

1. Prove generic proposition-indexed marginal projection for
   `ConflictIncidenceN`.
2. Formalize the generic rank / dimension argument separately from the finite
   arithmetic core.
3. Define pairwise and higher-order co-conflict observables.
4. Test a Möbius-transform representation for conflict interactions.
5. Characterize which interaction coordinates are forced to vanish under
   independence, exchangeability, or disjoint-carrier assumptions.
6. Determine how those restrictions shrink the fixed-marginal fibers.
