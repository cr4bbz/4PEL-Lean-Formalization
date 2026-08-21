# Paradoxes as failures of structural transport

Status: active research program on `research/preface-case-study`.

## Working thesis

The original heuristic, "paradoxes as projection errors", explains the Lottery
and Preface cases well but is too narrow.  The broader pattern is that a
paradoxical argument often presupposes that some epistemically relevant
property is preserved across a transformation.

Schematically:

```text
rich structure E  --T-->  transformed structure E'
     |                         |
     pi                        pi
     v                         v
coarse state S  --T*-->   coarse state S'
```

A paradoxical inference often behaves as if

```text
pi (T E) = T* (pi E)
```

must hold.  4-PEL lets us test this rather than assume it.  The characteristic
failure modes currently visible in the repository are:

- projection loss,
- non-commutation,
- nonclassical fixed points,
- threshold phase changes,
- dynamic status changes,
- higher-order interaction loss.

The phrase "failure of structural transport" is intentionally broader than
"projection error": it includes fixed-point and dynamic cases where no simple
forgetful projection is involved.

## Current paradox map

| Paradox / family | Transformation under pressure | 4-PEL diagnosis |
| --- | --- | --- |
| Lottery | thresholding vs conjunction | non-commutation |
| Preface | local marginals vs global interaction structure | projection loss / fiber underdetermination |
| Moore | object-level truth vs belief status | level separation |
| Liar | self-reference in a bivalent target space | glut-compatible fixed behavior without explosion |
| Knower | epistemic self-reference | four-valued fixed-point bifurcation |
| Sorites | continuous/small evidence change vs categorical status | threshold gap/glut geometry |
| Surprise Examination | sequential update vs preservation of present epistemic status | dynamic threshold crossing (planned) |
| Fitch | knowability vs actual knowledge | modal-epistemic transport; requires new operators (planned) |

## Knower: fixed-point bifurcation

`PEL4/Paradoxes/Knower.lean` introduces a strict one-world model with threshold
1 and studies the self-referential map induced by

```text
K := not B(K).
```

The candidate classification is:

```text
T -> F
F -> T
B -> B
N -> N
```

Thus the two nonclassical values are fixed points while the two classical
values form a 2-cycle.  If the module builds, the result supports the following
interpretation:

- `B` is stabilization by epistemic overdetermination;
- `N` is stabilization by epistemic underdetermination.

This also exposes a crucial semantic distinction for later work:

```text
internal FDE negation of B(phi)
```

is not automatically identical to

```text
absence of positive belief in phi.
```

That distinction matters for Moore, Knower, Fitch and Surprise-style formulas.

## Sorites: the threshold slack 2c - 100

`PEL4/Paradoxes/Sorites.lean` studies exclusive signed evidence on a scaled
0--100 line:

```text
positive = x
negative = 100 - x.
```

For a majority threshold `c > 50`, the gappy band is

```text
100 - c < x < c.
```

Its algebraic width is

```text
c - (100 - c) = 2c - 100.
```

The existing 4-PEL glut-boundary theorem already proves that when positive and
negative evidence overlap sufficiently for both to reach threshold, the glut
mass must satisfy

```text
P_B >= 2c - 100.
```

Hence the same threshold slack controls two opposite regimes:

- exclusive evidence: `2c - 100` is the gap width;
- overlapping evidence: `2c - 100` is the compulsory glut-overlap lower bound.

Working name: **Gap--Glut Threshold Duality**.

The philosophical claim is deliberately weaker than identifying vagueness with
probability.  The formal result concerns signed-evidence threshold geometry;
Sorites is an application of that geometry.

## Surprise Examination: next dynamic target

The repository already has `conditionalize` and product-update machinery.  A
minimal Surprise model should represent possible exam days as worlds and model
successive public evidence such as "no exam today" by updates.

The target phenomenon is not simple forgetting.  We want a formula `A`
representing the original announcement such that, along an update path,

```text
B_M0(A) = T
```

but at a later state

```text
B_Mk(A) = N or F.
```

This would make the Surprise paradox a dynamic version of the existing
Cartography idea: the epistemic state moves through probability space and
crosses a threshold boundary.

A stronger later target is to compare backward-elimination reasoning with the
actual update trajectory and identify the exact non-commuting square.

## Fitch: defer until epistemic architecture is clean

Standard Fitch reasoning needs more than the present language supplies.  In
particular it uses a knowledge operator `K`, modal possibility `Diamond`,
factivity, and distribution of knowledge over conjunction.

The current object language only has a threshold-belief operator.  Therefore a
faithful Fitch formalization should not be simulated by silently reusing `bel`.
Instead, Fitch should motivate a principled extension separating:

- probabilistic belief `B`,
- knowledge `K`,
- modal possibility / knowability,
- internal negation,
- meta-level absence of epistemic support.

Only after these distinctions are explicit should the paraconsistent Fitch
question be tested: whether `Kp and not Kp` must be impossible or may instead be
a controlled glut.

## Conflict Nerve connection

The new transport thesis also subsumes the Preface conflict geometry.  The
full representations

```text
exact incidence x_A
<-> co-conflict hierarchy J_A
<-> weighted filtration f(A)
```

are information-equivalent, whereas first-order marginals, `(q,r)`, support
nerves, Euler characteristics and later persistence summaries are progressively
coarser projections.

This gives a precise family of maps at which epistemic structure can be lost.
The emerging research question is therefore:

> Which paradoxes are generated or amplified when a rich epistemic structure
> is replaced by a coarser representation that fails to preserve the operation
> used in the argument?

## Literature anchors

The research direction is intended to connect with established work rather
than rename it:

- Kaplan and Montague on the Knower paradox;
- the Stanford Encyclopedia of Philosophy entries on self-reference and
  epistemic paradoxes;
- gap, glut, many-valued and paraconsistent approaches to the Sorites;
- standard dynamic analyses of the Surprise Examination;
- Church/Fitch knowability reasoning and paraconsistent revisions of its
  reductio step.

Novelty claims should be withheld until a systematic literature review checks
whether the combined signed-threshold / conflict-fiber / transport framework
has direct precedents.

## Immediate gate

Before extending to Surprise Examination, run `lake build` with the new Knower
and Sorites modules imported from `PEL4.lean`.  Until that succeeds, their
results are build candidates rather than compiler-verified theorems.
