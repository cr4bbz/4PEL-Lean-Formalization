# Preface Sharpness and Latent-Conflict Topology

## Status

This note continues the signed Preface programme after the latent-conflict carrier theorem.

For a finite conjunction

```text
C = p1 & ... & pn
```

4-PEL already establishes the carrier lower bound

```text
P(exists i : pi = B) >= 2c - 1
```

whenever belief in the conjunction is globally `B` at Lockean threshold `c > 1/2`.

The present step asks when this bound is exact and what remains free after exactness is imposed.

## Exact sharpness decomposition

Let the joint conjunction have FDE probability cells

```text
T = t
B = b
N = n
F = f
```

with total mass one. Write

```text
P_pos(C) = c + delta_pos
P_neg(C) = c + delta_neg
```

and let

```text
L = P(exists i : pi = B)
```

be the local conflict-carrier mass. Since every joint-B world is a local carrier world, write

```text
L = P_B(C) + W
```

where `W >= 0` is local glut mass that does not contribute to a joint conjunction glut.

Using

```text
P_pos(C) + P_neg(C) = 1 - P_N(C) + P_B(C),
```

we obtain the exact identity

```text
L = (2c - 1)
  + delta_pos
  + delta_neg
  + P_N(C)
  + W.
```

`PEL4/Paradoxes/PrefaceSharpness.lean` proves the denominator-free finite-count version:

```text
m + carrier
  = 2*k + deltaPos + deltaNeg + N + waste.
```

This decomposes every departure from the minimum into four non-negative sources:

1. positive threshold overshoot,
2. negative threshold overshoot,
3. joint gap mass,
4. unused local conflict.

## Sharpness characterization

The lower bound is exact,

```text
L = 2c - 1,
```

iff all four inefficiency terms vanish:

```text
delta_pos = 0
delta_neg = 0
P_N(C) = 0
W = 0.
```

Thus a minimally supported global conflict has a precise structural meaning:

* positive support hits the threshold exactly,
* negative support hits the threshold exactly,
* there are no joint gap worlds,
* every local conflict-carrier world actually contributes to the joint glut.

## The sharp conflict spine

Under sharpness the global FDE macrostate is forced to be

```text
(P_T, P_B, P_N, P_F)
  = (1-c, 2c-1, 0, 1-c).
```

Equivalently, in denominator-free form Lean proves

```text
T + k = m
F + k = m
m + B = 2k
N = 0.
```

As `c` moves from `1/2` to `1`, sharp global conflicts trace a line segment in the FDE probability simplex:

```text
(1/2, 0, 0, 1/2)
        ->
(0, 1, 0, 0).
```

This line is provisionally called the **Sharp Conflict Spine**.

## Macrostate does not determine microstructure

Sharpness fixes the global distribution but does not determine how the local glut carrier is distributed among conjuncts.

For three claims, let

```text
d  = local carrier mass
b1 = P_B(p1)
b2 = P_B(p2)
b3 = P_B(p3).
```

Then

```text
d <= b1 + b2 + b3
```

and each

```text
bi <= d.
```

The branch now records three extreme realizations with the same carrier mass `d = 3` in finite counts:

### Distributed

```text
(b1,b2,b3) = (1,1,1)
```

The carrier is spread evenly with no redundancy.

### Concentrated

```text
(b1,b2,b3) = (3,0,0)
```

One proposition carries the whole local conflict region.

### Redundant

```text
(b1,b2,b3) = (3,3,3)
```

Every carrier world is glutty in every proposition.

All three can support the same global sharp `B` macrostate.

## Latent-Conflict Triangle

Let

```text
peak  = max_i bi
sumB  = sum_i bi.
```

For `n` claims and sharp carrier mass `d`, define the normalized coordinates

```text
q = (n*peak - d) / ((n-1)*d)
r = (sumB - d) / ((n-1)*d).
```

Their intended readings are:

* `q`: concentration,
* `r`: redundancy.

The raw inequality

```text
sumB <= n * peak
```

implies

```text
0 <= r <= q <= 1.
```

For three claims this produces a triangular feasible region with extreme points:

```text
(0,0)  maximally distributed, non-redundant
(1,0)  maximally concentrated, non-redundant
(1,1)  maximally redundant.
```

`PrefaceSharpness.lean` proves the three-claim raw bound `totalLocal <= 3*peak` and includes witnesses for all three extreme shapes.

## Philosophical interpretation

The results separate three levels of epistemic description:

```text
local threshold-belief profile
        |
        v
global signed-evidence macrostate
        |
        v
local conflict topology.
```

Two agents can agree on every local threshold belief and can even have the same globally sharp four-valued conjunction state while differing radically in the internal organization of the evidence conflict.

This motivates a stronger claim than the earlier local-acceptance underdetermination result:

> Global four-valued evidence and minimal conflict mass still underdetermine the topology of the local conflict that realizes them.

The distinction between **concentrated** and **redundant** conflict is especially important. Both can have maximum concentration, but only redundant conflict is simultaneously present in many conjuncts on the same carrier worlds.

## Next targets

1. Generalize the topology theorem from three claims to arbitrary finite `n`.
2. Replace finite uniform counts by the repository's probability-measure layer.
3. Construct explicit signed Preface models realizing interior points of the latent-conflict triangle.
4. Determine which additional assumptions collapse the triangle, e.g. disjoint local-glut carriers, bounded overlap, or evidential independence.
5. Compare this geometry with the classical Preface, Lottery, and Moore case studies.
