# Epistemic status and structural transport

Status: verified core architecture with Moore/Knower integration as the next build gate on `research/preface-case-study`.

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
`N`. `PEL4/EpistemicStatus.lean` makes this distinction explicit.

## Verified status vocabulary

The Lean 4.31 build verifies the layer containing:

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

None of these is identified with factive knowledge.

## Verified separation theorem

Lean verifies

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

This turns the earlier semantic caution into a machine-checked theorem.

## Verified structural transport vocabulary

`PEL4/StructuralTransport.lean` introduces the domain-agnostic notions

```text
TransportsPredicate T P Q
PreservesPredicate T P
Commutes pi T Tstar
PreservesObservation T observeSource observeTarget
```

with generic witness theorems for refuting preservation and commutation claims.

The Surprise backward-elimination development is now the first verified
paradox-level instantiation: its branch-relative prediction predicate fails to
transport to the initial prediction predicate.

Thus "structural transport failure" is no longer used only as philosophical
prose. It is an explicit formal property that paradox modules can instantiate.

## Moore integration: next build gate

`PEL4/Paradoxes/Moore.lean` now separates two readings that classical notation
can blur:

```text
object-language: p and not B(p)
```

and

```text
meta-level: p has positive truth support and positive belief in p is absent.
```

In the existing 1/2--1/2 model at threshold 2/3, the new candidate theorems say:

```text
B(p) = N
not B(p) = N
p and not B(p) = N
lackPositiveBelief(p) = true
lackNegativeBelief(p) = true
meta-level Moore condition = true.
```

If the next build succeeds, the repository will formally distinguish a gappy
internal Moore sentence from a satisfied meta-level absence-of-belief condition.

## Knower integration: next build gate

`PEL4/Paradoxes/Knower.lean` now uses the status layer to sharpen what its fixed
point equation represents.

The already verified map

```text
T -> F
F -> T
B -> B
N -> N
```

implements internal FDE negation of threshold belief. The new candidate theorem
says that the positive bit of this internal negation matches meta-level absence
of positive belief exactly on the classical states.

Hence the two nonclassical fixed points also witness two opposite divergences:

```text
B: internal not is positively supported; positive belief is not absent.
N: internal not lacks positive support; positive belief is absent.
```

This means a natural-language Knower sentence using "not known" or "not
believed" cannot be treated as semantically settled until the intended notion
of epistemic negation is specified.

## Roadmap toward Fitch

The intended sequence is now:

1. verify the Moore and Knower reuse of the status layer;
2. perform a strict semantic/literature gate for a genuinely distinct knowledge
   operator `K` rather than aliasing threshold belief;
3. specify factivity and the intended conjunction principles for `K`;
4. introduce modal possibility / knowability separately;
5. distinguish internal `not K(phi)` from meta-level absence of knowledge;
6. formalize Fitch only after those choices are explicit.

The design constraint remains:

```text
belief != absence of belief != disbelief != knowledge.
```

In a four-valued semantics these distinctions correspond to different bit-level
and modal structures. Collapsing them can manufacture or erase paradoxical
inferences.
