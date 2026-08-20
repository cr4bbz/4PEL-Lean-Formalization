# Signed Preface Taxonomy

## Purpose

P1 and P2 established the classical geometric core of the Preface paradox.  In
the one-error family, local acceptance and global fallibility occupy a clipped
probability simplex with exact threshold boundary

```text
c <= n/(n+1).
```

P3 asks a different question: what changes when the underlying evidence is
genuinely four-valued rather than merely classical T/F evidence embedded into
FDE?

The answer is not just that more valuations become available.  The same locally
accepted corpus can now have several qualitatively different global epistemic
states.

## Signed evidence plane

For any formula `phi`, 4-PEL tracks two threshold-relevant masses:

```text
P_pos(phi)
P_neg(phi)
```

with a Lockean threshold `c`.

This divides the evidence plane into four regions:

```text
T : P_pos >= c and P_neg < c
F : P_pos <  c and P_neg >= c
B : P_pos >= c and P_neg >= c
N : P_pos <  c and P_neg <  c
```

`PEL4/Paradoxes/PrefaceSigned.lean` formalizes this as `SignedMassCell` and
proves `threshold_exhaustive`.

## Three globally different corpora with the same local profile

The control models use three claims, five equiprobable worlds, and the same
threshold:

```text
c = 3/5.
```

In all three models:

```text
B(p1) = T
B(p2) = T
B(p3) = T.
```

So the author has exactly the same local threshold-acceptance profile.

Nevertheless the belief state of the conjunction differs.

### Type F: rejection / classical Preface fracture

The conjunction is positively supported in two worlds and negatively supported
in three:

```text
P_pos(p1 & p2 & p3) = 2/5
P_neg(p1 & p2 & p3) = 3/5
```

therefore:

```text
B(p1 & p2 & p3) = F.
```

The corresponding fallibility claim has state `T`.

This is the classical Preface pattern: every claim is individually accepted,
but the corpus as a conjunction is rejected and its negation is accepted.

### Type N: global underdetermination

The conjunction is positively supported in two worlds and has no negative
support in the remaining three because those worlds contain gaps rather than
falsity:

```text
P_pos(p1 & p2 & p3) = 2/5
P_neg(p1 & p2 & p3) = 0.
```

therefore:

```text
B(p1 & p2 & p3) = N.
```

The fallibility claim is also `N`.

The corpus is locally accepted but globally neither accepted nor rejected.  The
problem is no longer inconsistency; it is insufficient determination at the
joint level.

### Type B: global overdetermination

The conjunction has two T-worlds, one B-world, and two F-worlds:

```text
P_pos(p1 & p2 & p3) = 3/5
P_neg(p1 & p2 & p3) = 3/5.
```

therefore:

```text
B(p1 & p2 & p3) = B.
```

The fallibility claim is also `B` because FDE negation fixes the glut state.

Crucially, every individual belief remains `T`.  Hence global epistemic glut can
emerge without any local belief glut.

## Quantitative glut signature

For a finite signed evidence cell with masses

```text
T = t
B = b
N = n
F = f
```

and total mass `m`, positive and negative support are:

```text
P_pos = t + b
P_neg = f + b.
```

If both cross threshold `k`, `PrefaceSigned.lean` proves:

```text
2*k <= m + b.
```

Equivalently, in normalized probability notation:

```text
P_B >= 2c - 1.
```

At a strict-majority threshold this implies:

```text
P_B > 0.
```

So a global glut cannot be manufactured by two disjoint large evidence piles.
Some probability mass must genuinely support both sides.

The P3 control model is tight:

```text
m = 5
k = 3
b = 1
```

and hence:

```text
b = 2k - m.
```

It realizes the smallest possible overlap mass compatible with global state B.

## Philosophical result

The original Preface formulation treats the failure of joint acceptance as one
kind of incoherence.  P3 shows that this collapses at least three distinct
structures:

```text
F : global rejection
N : global underdetermination
B : global overdetermination / conflict
```

while holding fixed:

```text
local threshold
number of claims
local belief state T for every claim.
```

This motivates a distinction between **local acceptance profile** and **global
epistemic mode**.

A single vector

```text
(B(p1), ..., B(pn))
```

is therefore not sufficient to characterize the epistemic status of the corpus.
The joint proposition carries irreducible information.

A useful provisional taxonomy is:

1. **Rejection fracture** — local T, joint F.
2. **Determination gap** — local T, joint N.
3. **Conflict saturation** — local T, joint B.

The familiar Preface paradox is only the first member.

## Stronger working hypothesis

The four-valued framework suggests that "epistemic incoherence" should not be
modeled as a binary property.  It may instead have at least two independent
axes:

```text
acceptance failure  <-> acceptance success
negative support    <-> negative support failure
```

or, geometrically, location relative to the two threshold hyperplanes

```text
P_pos = c
P_neg = c.
```

The classical Preface paradox occupies only one quadrant of this geometry.

## Next experiments

### P3a — Local/global glut separation

Determine exact conditions under which all local beliefs are T while the joint
belief is B.  Seek an `n`-claim lower bound on the amount and placement of
object-level B-mass required.

### P3b — Joint-gap region

Characterize when all local beliefs are T but the conjunction is N.  Compare
this with the classical simplex region and identify whether gap mass enlarges
the feasible threshold range.

### P3c — Four-valued threshold phase diagram

For fixed `n`, map the attainable global states T/F/B/N as functions of:

```text
c
P_B
P_N
error distribution.
```

The target is a phase diagram rather than a catalogue of examples.

### P3d — Recovery conditions

Search for additional assumptions under which local T forces the joint state
back toward a unique classical outcome.  Candidate restrictions include:

```text
no object-level gluts
no object-level gaps
independence assumptions
bounded overlap
closure principles.
```

This is the direct analogue of the assumption-control method used in
`goedel-4pel`.
