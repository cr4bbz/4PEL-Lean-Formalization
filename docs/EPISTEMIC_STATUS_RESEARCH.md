# Epistemic status and structural transport

Status: active build candidate on `research/preface-case-study`.

## Why this layer exists

Several paradoxes in the repository depend on expressions such as "does not
believe", "believes false", "is uncertain", or later "does not know". In a
four-valued setting these notions cannot safely be collapsed.

For a belief state

```text
v = (positive support, negative support),
```

internal FDE negation swaps the bits:

```text
not v = (negative support, positive support).
```

By contrast, meta-level absence of positive belief is

```text
not (positive support).
```

These coincide on the classical values `T` and `F`, but disagree on `B` and
`N`. The new `PEL4/EpistemicStatus.lean` module makes this distinction explicit.

## Build-candidate status vocabulary

The current layer names:

```text
positivelyBelieves
negativelyBelieves
lacksPositiveBelief
lacksNegativeBelief
strictlyPositivelyBelieves
strictlyNegativelyBelieves
hasGluttyBelief
hasGappyBelief
```

The intended interpretation is deliberately modest:

- positive belief = positive threshold support;
- negative belief = negative threshold support;
- lack of positive belief = failure of the positive threshold;
- strict disbelief = negative support without positive support;
- glut and gap retain the ordinary four-valued readings.

None of these is yet identified with factive knowledge.

## Separation theorem

The principal candidate theorem is

```text
(FDE.not v).pos = not v.pos
    iff
v is classical.
```

Equivalently, internal negation behaves like simple absence of positive support
exactly on the classical subspace `{T,F}`. The nonclassical states are precisely
where the distinction becomes visible:

```text
B: internal negation remains positively supported,
   but positive belief is not absent.

N: internal negation is not positively supported,
   but positive belief is absent.
```

If the next `lake build` succeeds, this turns an earlier semantic caution into
a machine-checked theorem.

## Structural transport as a formal object

`PEL4/StructuralTransport.lean` introduces a domain-agnostic vocabulary:

```text
TransportsPredicate T P Q
PreservesPredicate T P
Commutes pi T Tstar
PreservesObservation T observeSource observeTarget
```

with generic witness theorems for refuting each preservation claim.

The point is to stop using "transport failure" only as philosophical prose.
Paradox modules should increasingly instantiate these generic definitions.

## First paradox-level instantiation

The Surprise backward-elimination module now defines

```text
backwardPredictionTransport
```

as transport from

```text
predictable in the day-specific elimination context
```

to

```text
predictable in the initial context.
```

The new candidate theorem

```text
not backwardPredictionTransport
```

uses the already verified Friday witness:

```text
backward-context prediction = true
initial-context prediction  = false.
```

If this builds, Surprise becomes the first paradox for which the repository
proves a failure using the generic structural-transport language itself.

## Roadmap toward Fitch

The intended sequence is:

1. verify the epistemic-status separation layer;
2. reuse it in Moore, Knower, and Surprise where appropriate;
3. specify a genuinely distinct knowledge operator `K` rather than aliasing
   threshold belief;
4. specify factivity and the intended conjunction principles for `K`;
5. introduce modal possibility / knowability separately;
6. formalize Fitch only after the meanings of
   `not K(phi)` and absence of knowledge are explicitly distinguished.

The design constraint is simple:

```text
belief != absence of belief != disbelief != knowledge.
```

This is not merely terminology. In a four-valued semantics these distinctions
correspond to different bit-level and modal structures, and collapsing them can
manufacture or erase paradoxical inferences.
