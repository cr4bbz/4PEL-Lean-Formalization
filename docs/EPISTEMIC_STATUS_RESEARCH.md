# Epistemic status and structural transport

Status: verified core architecture with verified Moore, Knower, and Surprise reuse on `research/preface-case-study`.

## Why this layer exists

Several paradoxes in the repository depend on expressions such as "does not believe", "believes false", "is uncertain", or later "does not know". In a four-valued setting these notions cannot safely be collapsed.

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

These coincide on the classical values `T` and `F`, but disagree on `B` and `N`. `PEL4/EpistemicStatus.lean` makes this distinction explicit.

## Verified status vocabulary

The Lean 4.31 build verifies:

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

Equivalently, internal negation behaves like simple absence of positive support exactly on the classical subspace `{T,F}`. The nonclassical states are precisely where the distinction becomes visible:

```text
B: internal negation remains positively supported,
   but positive belief is not absent.

N: internal negation is not positively supported,
   but positive belief is absent.
```

This is now a machine-checked structural fact of the 4-PEL architecture.

## Verified structural transport vocabulary

`PEL4/StructuralTransport.lean` introduces the domain-agnostic notions

```text
TransportsPredicate T P Q
PreservesPredicate T P
Commutes pi T Tstar
PreservesObservation T observeSource observeTarget
```

with generic witness theorems for refuting preservation and commutation claims.

The Surprise backward-elimination development is the first verified paradox-level instantiation: branch-relative prediction fails to transport to initial-context prediction.

Thus "structural transport failure" is not only philosophical prose. It is an explicit formal property that paradox modules can instantiate.

## Verified Moore integration

`PEL4/Paradoxes/Moore.lean` now separates two readings that classical notation can blur:

```text
object-language: p and not B(p)
```

and

```text
meta-level: p has positive truth support and positive belief in p is absent.
```

In the existing 1/2--1/2 model at threshold 2/3, Lean verifies:

```text
B(p) = N
not B(p) = N
p and not B(p) = N
lackPositiveBelief(p) = true
lackNegativeBelief(p) = true
meta-level Moore condition = true.
```

Hence the internal Moore formula is gappy while the meta-level absence-of-belief condition is satisfied. This is a genuine semantic separation, not merely a terminological distinction.

## Verified Knower integration

`PEL4/Paradoxes/Knower.lean` uses the same status layer to sharpen what its fixed-point equation represents.

The verified map

```text
T -> F
F -> T
B -> B
N -> N
```

implements internal FDE negation of threshold belief. Lean also verifies that the positive bit of this internal negation matches meta-level absence of positive belief exactly on the classical states.

Thus the two nonclassical fixed points witness opposite divergences:

```text
B: internal not is positively supported; positive belief is not absent.
N: internal not lacks positive support; positive belief is absent.
```

A natural-language Knower sentence using "not known" or "not believed" therefore remains semantically ambiguous until the intended epistemic negation is specified.

## Knowledge semantics gate

The next stage is no longer to add more status predicates. It is to introduce knowledge only after a literature-grounded semantic choice.

See:

```text
docs/KNOWLEDGE_SEMANTICS_GATE.md
```

The current design constraint is:

```text
belief != absence of belief != disbelief != knowledge.
```

The preferred next sequence is:

1. compare standard modal-FDE `Box` with evidence-stable knowledge semantics;
2. introduce a distinct candidate `K` without reusing the Lockean threshold operator;
3. test factivity, conjunction principles, classical recovery, glut/gap behavior, and negation separation;
4. introduce raw modal possibility separately from any De-Morgan dual;
5. only then formalize Fitch.

This ordering is deliberate. In four-valued epistemic logic, collapsing these distinctions can manufacture or erase paradoxical inferences.
