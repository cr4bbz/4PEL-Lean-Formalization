# Latent Conflict in the Signed Preface Case

## Research question

P3 established that all local threshold beliefs can remain `T` while the belief
state of their conjunction is `B`.

The remaining question was whether such a global epistemic glut can arise
without any object-level local glut, or whether some hidden local conflict must
be present below the belief threshold.

The answer is now exact for the three-claim finite uniform case.

## Pointwise FDE fact

For

```text
C = p1 and p2 and p3
```

FDE conjunction has positive support at a world exactly when every conjunct has
positive support, and negative support exactly when at least one conjunct has
negative support.

Therefore:

```text
C = B at a world
```

implies:

```text
at least one pi = B at that world.
```

A conjunction glut cannot appear ex nihilo. Every world contributing to the
joint glut is carried by at least one local object-level glut.

`PEL4/Paradoxes/PrefaceLatentConflict.lean` proves this as:

```text
and3_glut_implies_some_local_glut
```

and lifts it from worlds to finite masses via:

```text
joint_glut_count_le_local_carrier.
```

## Latent Conflict Carrier Theorem

Let a finite uniform model have `m` worlds and threshold `k/m`. Suppose belief
in the conjunction is `B`, so both its positive and negative world counts reach
`k`.

Then:

```text
2*k <= m + localCarrier
```

where `localCarrier` is the number of worlds in which at least one conjunct is
object-level `B`.

Normalized:

```text
P(exists i : pi = B) >= 2c - 1.
```

This is stronger than the original conjecture because it bounds the union of
local conflict worlds, not merely the sum of their individual masses.

At every strict-majority threshold `c > 1/2`, global `B` therefore entails a
strictly positive local conflict carrier.

## Original conjecture as a corollary

Since the probability of a union is at most the sum of the individual masses:

```text
P(exists i : pi = B)
    <= P_B(p1) + P_B(p2) + P_B(p3),
```

the carrier theorem yields:

```text
P_B(p1) + P_B(p2) + P_B(p3) >= 2c - 1.
```

The Lean theorem is:

```text
local_glut_sum_budget.
```

Thus the conjectured local glut budget is confirmed for the three-claim finite
uniform signed Preface family.

## Pigeonhole localization

A further consequence is that at least one proposition must carry at least one
third of the required conflict budget:

```text
exists i : P_B(pi) >= (2c - 1)/3.
```

The integer-scaled Lean form is:

```text
some_local_glut_carries_third_budget.
```

This does not say that any local belief is `B`. A local belief becomes `B` only
when both its positive and negative masses cross `c`. The theorem bounds the
object-level `B` mass, which can remain strictly below the local negative
threshold.

That difference is the central phenomenon.

## Latent versus manifest conflict

This motivates two levels of conflict.

### Latent local conflict

There is object-level `B` mass associated with one or more individual claims,
but it remains below the threshold needed to turn any `B(pi)` into epistemic
state `B`.

### Manifest global conflict

After conjunction, the positive and negative evidence profiles aggregate so
that both cross the threshold:

```text
B(p1 and p2 and p3) = B.
```

Hence:

```text
local belief profile:   (T, T, T)
joint belief state:      B
```

is compatible with, and indeed requires, hidden object-level contradiction.

## Philosophical result

A useful formulation is:

> Global epistemic conflict can be locally epistemically invisible, but it
> cannot be locally evidentially ungrounded.

The first clause is witnessed by the signed Preface control model: every local
belief is `T` while the conjunction is `B`.

The second clause is proved by the latent conflict carrier theorem: at least
`2c-1` of the probability space must contain an object-level glut in one or more
conjuncts.

This separates two notions that are easy to collapse:

```text
absence of local belief conflict
```

and

```text
absence of local contradictory evidence.
```

They are not equivalent.

## Relation to the existing 4-PEL glut boundary

The repository already proves the general conflict-mass boundary for a single
formula:

```text
P_B(phi) >= 2c - 1
```

whenever its positive and negative evidence both cross the Lockean threshold.

The new result adds a structural descent principle for conjunction:

```text
joint epistemic B
    -> joint object-level B mass >= 2c-1
    -> local conflict carrier mass >= 2c-1
    -> summed local B mass >= 2c-1.
```

So the conflict budget can be traced from the global belief state back into the
local conjuncts.

## Next target: n-claim descent

The three-claim result strongly suggests the general theorem:

```text
B(p1 and ... and pn) = B
-> P(exists i : pi = B) >= 2c - 1
-> sum_i P_B(pi) >= 2c - 1
-> exists i : P_B(pi) >= (2c - 1)/n.
```

The pointwise FDE step already has the right shape for arbitrary finite
conjunctions. The remaining task is to generalize the current `and3` and finite
count machinery to lists of conjuncts.

If successful, this would yield an n-dimensional latent-conflict theorem rather
than a three-claim case study.
