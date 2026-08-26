# Paradoxes as failures of structural transport

Status: active research program carried forward on `research/complex-coordinates`.

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

must hold. 4-PEL lets us test this rather than assume it.

The characteristic failure modes currently visible in the repository are:

- projection loss,
- non-commutation,
- nonclassical fixed points,
- threshold phase changes,
- dynamic status changes,
- higher-order interaction loss,
- context-collapse across counterfactual epistemic branches,
- stability-reflection failure from compounds to components,
- collapse of four-valued modal information under internal dualization.

The phrase **failure of structural transport** is intentionally broader than
"projection error": it includes fixed-point, modal, and dynamic cases where no
simple forgetful projection is involved.

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
| Surprise backward elimination | branch-relative prediction vs initial prediction | context-collapse / failed prediction transport | verified |
| Fitch | knowledge of a Moorean compound vs knowledge of components | stability-reflection failure; modal duality boundary | local fracture + recovery verified; global boundary current gate |

## Knowledge as a transport-sensitive operator

The Fitch project forced the repository to distinguish probabilistic belief from
knowledge. The evidence-stable knowledge candidate evaluates the complete FDE
profile across accessible worlds.

Compiler-verified behavior includes:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N
heterogeneous full FDE status -> K(phi) = F.
```

The key structural predicate is therefore full-value stability.

This produces a directional conjunction law:

```text
K+(phi) and K+(psi) -> K+(phi and psi)
```

but not unrestricted elimination. Under positive knowledge of the conjunction,
Lean verifies the exact boundary:

```text
K+(phi) iff Stable(phi)
K+(psi) iff Stable(psi).
```

Working diagnosis: **stability reflection boundary**. Composition preserves
stability, but a stable compound need not reveal stable components.

## Modal possibility: verified duality boundary

The modal extension keeps primitive raw accessibility possibility separate from
the internal expression

```text
not K(not phi).
```

Lean verifies that internal negation preserves accessible full-value stability.
Under instability, evidence-stable knowledge of `not phi` becomes strict `F`, so
its internal negation becomes strict `T`.

Hence raw possibility and the internal knowledge dual can diverge on glutty and
gappy profiles. The exact verified boundary is:

```text
Diamond_raw(phi) = not K(not phi)
iff
Stable(phi) OR Diamond_raw(phi) = T.
```

This reveals a second transport failure relevant to Fitch: classical modal
dualization can erase four-valued information by converting epistemic
heterogeneity into strict truth.

## Fitch: verified local fracture and recovery boundary

`PEL4/ModalLanguage.lean` introduces primitive object-language `K` and primitive
raw `Diamond` as a conservative extension of the earlier formula language.

`PEL4/Paradoxes/Fitch.lean` then formalizes the actual Moorean formula

```text
M(phi) = phi and not K(phi).
```

The finite Fitch model contains a reflexive critical witness with:

```text
K(M(p)) = B
K(p)    = F
K(not K(p)) = F.
```

Thus positive knowledge of the Moorean conjunction does not transport to
positive knowledge of either component, even at a reflexive point.

The semantic mechanism is verified directly:

```text
Stable(M(p))     = true
Stable(p)        = false
Stable(not K(p)) = false.
```

The classical Fitch contradiction therefore fails to arise in that model not
because factivity is absent, but because compound stability fails to reflect to
its components.

`PEL4/Paradoxes/FitchRecovery.lean` proves the converse local result. At a point
with positive knowledge of

```text
phi and not K(phi),
```

the package

```text
reflexivity
+ Stable(phi)
+ no-glut condition for K(phi)
```

is inconsistent.

The existing Fitch witness satisfies reflexivity and local no-glut while
violating `Stable(p)`. Thus its concrete escape route from the classical
collision is specifically component instability.

The next build gate, `PEL4/Paradoxes/FitchKnowabilityBoundary.lean`, lifts this
through primitive raw possibility. Its target global statement is:

```text
Diamond_raw+ K(phi and not K phi)
-> some accessible positive knowledge witness violates the local recovery package.
```

The global module must not be marked verified until a successful local build is
reported.

## Knower: fixed-point bifurcation

`PEL4/Paradoxes/Knower.lean` introduces a strict one-world model with threshold
1 and studies the self-referential map induced by

```text
K := not B(K).
```

The Lean 4.31 build verifies:

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

Working diagnosis: **epistemic fixed-point bifurcation**.

## Sorites: the threshold slack 2c - 100

`PEL4/Paradoxes/Sorites.lean` studies exclusive signed evidence on a scaled
0--100 line:

```text
positive = x
negative = 100 - x.
```

For a majority threshold `c > 50`, Lean verifies that the gappy band is exactly

```text
100 - c < x < c
```

with width

```text
2c - 100.
```

The existing glut-boundary theorem shows that the same threshold slack is the
minimum overlap mass required when positive and negative evidence both reach
threshold.

Working diagnosis: **Gap--Glut Threshold Duality**.

## Surprise Examination: verified dynamic threshold reversal

`PEL4/Paradoxes/SurpriseExamination.lean` uses the existing `conditionalize`
machinery on three possible exam days with threshold `2/3`.

Successive truthful updates verify belief in "exam on Friday" as

```text
F -> N -> T
```

and belief in "not Friday" as

```text
T -> N -> F.
```

Additional truthful evidence therefore need not preserve categorical epistemic
status. The reversal passes through the gap state.

## Surprise backward elimination: verified context transport failure

`PEL4/Paradoxes/SurpriseBackwardElimination.lean` formalizes the local
justifications in their actual updated/counterfactual contexts.

Each day is positively predictable in the context used to eliminate it while
none is positively predicted in the initial model. Thus:

```text
predictable(day, elimination-context(day)) = true
predictable(day, initial context)          = false.
```

Working diagnosis: **context-collapse**. The classical backward argument
packages branch-relative predictions into one context-free eliminability
judgement and transports them back to the initial state.

## Preface conflict geometry and topology

The transport thesis also subsumes the Preface conflict program. The full
representations

```text
exact incidence x_A
<-> co-conflict hierarchy J_A
<-> weighted filtration f(A)
```

are information-equivalent, whereas first-order marginals, `(q,r)`, support
nerves, Euler characteristics, and later persistence summaries are progressively
coarser observations.

The generic fixed-marginal fiber has freedom

```text
2^n - n - 2
```

for `n >= 2`, quantifying the higher-order interaction structure invisible to
first-order marginals.

Lean also verifies finite profiles with identical coarse data but distinct
Conflict-Nerve support signatures and Euler counts. Working diagnosis:
**topological conflict underdetermination**.

General simplicial homology and persistence remain open.

## Emerging cross-paradox pattern

The strongest examples now share a three-stage research shape:

```text
1. identify a transport principle silently used by a paradoxical argument;
2. construct a finite witness where that transport fails;
3. characterize the additional hypotheses that recover the transport.
```

Fitch currently realizes this pattern most sharply:

```text
unrestricted K-conjunction extraction fails;
component stability restores extraction;
reflexivity + stability + no-glut restores the local classical collision.
```

The foundational next question is whether this pattern can itself be expressed
as reusable abstract Lean theorems over `StructuralTransport.lean` rather than
remaining a family resemblance between case studies.

## Literature and novelty boundary

The research direction is intended to connect with established work rather than
rename it. Relevant anchors include Belnap-Dunn logic, nonstandard epistemic
modalities, paraconsistent epistemic logic, Church-Fitch knowability, dynamic
epistemic logic, Lockean threshold belief, Möbius inversion, and simplicial
methods.

Novelty claims should be withheld until a systematic literature review checks
the exact status of the combined results and terminology. In particular, names
such as **Knowledge Stability Principle**, **Possibility Duality Collapse**,
**Stability Reflection Boundary**, and **Topological Conflict
Underdetermination** are currently project terminology.

## Research agenda

The detailed question map is maintained in `docs/RESEARCH_QUESTIONS.md`.
Near-term priorities are:

```text
1. compile the global Fitch knowability boundary
2. prove independence/minimality of the local Fitch recovery assumptions
3. formalize modal satisfaction/validity and the full Church-Fitch theorem schema
4. classify modal laws of evidence-stable K and raw Diamond
5. repair the zero-evidence update boundary before strong dynamic-K claims
6. generalize the structural-transport abstraction across paradox families
7. deepen conflict topology to homology and persistence
8. perform a systematic literature/novelty audit
```

The methodological rule remains: distinguish machine-checked theorem, finite
witness, structural interpretation, and novelty claim.
