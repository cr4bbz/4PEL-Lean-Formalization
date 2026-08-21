# Paradoxes as failures of structural transport

Status: active research program on `research/preface-case-study`.

## Working thesis

The original heuristic, "paradoxes as projection errors", explains the Lottery
and Preface cases well but is too narrow. The broader pattern is that a
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

must hold. 4-PEL lets us test this rather than assume it. The characteristic
failure modes currently visible in the repository are:

- projection loss,
- non-commutation,
- nonclassical fixed points,
- threshold phase changes,
- dynamic status changes,
- higher-order interaction loss,
- context-collapse across counterfactual epistemic branches.

The phrase "failure of structural transport" is intentionally broader than
"projection error": it includes fixed-point and dynamic cases where no simple
forgetful projection is involved.

## Current paradox map

| Paradox / family | Transformation under pressure | 4-PEL diagnosis | Status |
| --- | --- | --- | --- |
| Lottery | thresholding vs conjunction | non-commutation | verified |
| Preface | local marginals vs global interaction structure | projection loss / fiber underdetermination | verified |
| Moore | object-level truth vs belief status | level separation | executable model |
| Liar | self-reference in a bivalent target space | glut-compatible fixed behavior without explosion | executable + ex-falso theorem |
| Knower | epistemic self-reference | four-valued fixed-point bifurcation | verified |
| Sorites | continuous/small evidence change vs categorical status | threshold gap/glut geometry | verified |
| Surprise Examination | sequential update vs preservation of present epistemic status | dynamic threshold reversal | verified |
| Surprise backward elimination | branch-relative prediction vs initial prediction | context-collapse / failed prediction transport | build candidate |
| Fitch | knowability vs actual knowledge | modal-epistemic transport; requires new operators | planned |

## Knower: fixed-point bifurcation

`PEL4/Paradoxes/Knower.lean` introduces a strict one-world model with threshold
1 and studies the self-referential map induced by

```text
K := not B(K).
```

The Lean 4.31 build verifies the complete classification:

```text
T -> F
F -> T
B -> B
N -> N
```

Thus the two nonclassical values are fixed points while the two classical
values form a 2-cycle:

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

The Lean 4.31 build verifies that for a majority threshold `c > 50`, the gappy
band is exactly

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
probability. The formal result concerns signed-evidence threshold geometry;
Sorites is an application of that geometry.

## Surprise Examination: verified dynamic threshold reversal

`PEL4/Paradoxes/SurpriseExamination.lean` uses the existing `conditionalize`
machinery on three possible exam days: Monday, Wednesday, and Friday, initially
equiprobable with threshold `2/3`.

Successive truthful updates are:

```text
E1: not Monday
E2: not Wednesday
```

The Lean 4.31 build verifies belief in "exam on Friday" as

```text
F -> N -> T
```

and belief in "not Friday" as

```text
T -> N -> F.
```

Thus additional truthful evidence does not preserve categorical belief status.
The reversal passes through the gap state rather than jumping directly from one
determined pole to the other.

The module also separates internal FDE negation from a meta-level positive
prediction predicate. Initially no individual exam day is positively predicted;
after eliminating Monday and Wednesday, Friday is positively predicted.

This is not a complete formalization of the classical Surprise Examination
announcement, because the current language has probabilistic belief rather
than a separate factive knowledge operator. It formally isolates the dynamic
pressure point: eliminating alternatives can create predictability.

## Surprise backward elimination: context-indexed prediction

`PEL4/Paradoxes/SurpriseBackwardElimination.lean` is the next build candidate.
It formalizes the backward-elimination justifications in the distinct epistemic
contexts in which they are actually obtained:

```text
Friday:    predict in the actual late-week model after not-Monday and not-Wednesday
Wednesday: predict after hypothetically ruling out Friday and then learning not-Monday
Monday:    predict after hypothetically ruling out Friday and Wednesday
```

Each local prediction is expected to be correct. But the original model predicts
none of the three days individually.

The target theorem is therefore not that backward reasoning contains a locally
invalid prediction. It is that prediction fails to transport across contexts:

```text
predictable(day, its elimination context)
```

does not imply

```text
predictable(day, initial context).
```

Working diagnosis: **context-collapse**. The backward argument packages
predictions made in distinct updated/counterfactual models into a single
context-free eliminability judgement and transports that judgement back to the
initial epistemic state.

This would strengthen the Surprise analysis from simple non-monotonicity under
update to a precise failure of structural transport across epistemic contexts.

## Fitch: defer until epistemic architecture is clean

Standard Fitch reasoning needs more than the present language supplies. In
particular it uses a knowledge operator `K`, modal possibility `Diamond`,
factivity, and distribution of knowledge over conjunction.

The current object language only has a threshold-belief operator. Therefore a
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

The transport thesis also subsumes the Preface conflict geometry. The full
representations

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
- Surprise Test work centered on backward elimination and advance
  predictability;
- dynamic epistemic logic and public-announcement style model transformations;
- Church/Fitch knowability reasoning and paraconsistent revisions of its
  reductio step.

Novelty claims should be withheld until a systematic literature review checks
whether the combined signed-threshold / conflict-fiber / transport framework
has direct precedents.

## Immediate gate

Knower, Sorites, and the dynamic Surprise reversal are compiler-verified under
Lean 4.31. The next gate is `PEL4/Paradoxes/SurpriseBackwardElimination.lean`.
Until the next successful `lake build`, its context-collapse results remain
build candidates.
