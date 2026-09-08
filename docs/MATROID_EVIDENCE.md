# Matroidal Evidence in 4-PEL

Status: research gate on `research/matroid-evidence`

## Research question

Can the bilateral positive/negative evidence signature of 4-PEL support a
matroidal notion of evidential novelty and redundancy without changing the
underlying four-valued semantics?

## Gate 1 claim

Yes, at the coarse channel level.

Let `α` be evidence atoms and let

```text
polarity : α -> {positive, negative}.
```

Define closure by same-polarity generation:

```text
e ∈ cl(A)  iff  there exists a ∈ A with polarity(a) = polarity(e).
```

The Lean development proves that this closure is:

1. extensive,
2. monotone,
3. idempotent, and
4. exchange-satisfying.

Thus the positive and negative evidence classes form the canonical two-class
partition matroid induced by the coarse 4-PEL observation.

## Verified structural consequences

- Same-polarity atoms lie in one another's singleton closure.
- Adding all same-channel redundant atoms does not create a new positive or
  negative support channel.
- Therefore channel closure preserves the realized `FDEValue` exactly.
- The coarse channel-rank profile is:

```text
N -> 0
T -> 1
F -> 1
B -> 2
```

The last line is philosophically useful but modest: `B` has maximal coarse
channel breadth because both support directions are present. It does not follow
that `B` is better justified, more reliable, or informationally complete.

## Scope boundary

This gate does **not** claim that arbitrary evidence structures are matroids.
The result is induced specifically by the two Boolean observations already
present in the 4-PEL/FDE kernel. Multiple evidence atoms of the same polarity
are parallel only after this coarse projection. Source identity, inferential
origin, probability, reliability, and corroboration strength can distinguish
those atoms in a finer model.

## Formal files

```text
PEL4/MatroidEvidence.lean
PEL4/MatroidEvidenceAxiomAudit.lean
```

The root `PEL4.lean` imports both files so the full build checks the extension.

## Paper integration

The working manuscript version 0.5 adds:

```text
paper/sections/14_matroid_evidence.tex
```

It states the closure theorem, FDE-state conservativity, the channel-rank
profile, and the scope boundary. Whitney (1935) and Oxley (2011) are added as
standard matroid references.

## Next gates

### Gate 2: topological closure versus matroid closure

The repository already contains topological evidence closures. Determine exact
conditions under which a 4-PEL topological closure satisfies exchange and hence
is simultaneously matroidal.

### Gate 3: circuits as minimal evidential redundancy

Define circuits as minimal dependent evidence families and ask whether they
admit an epistemic interpretation such as minimal redundancy, minimal circular
support, or minimal overdetermination.

### Gate 4: deletion and contraction

Study deletion as removal/forgetting of evidence atoms and contraction as
quotienting by evidence taken as background. Compare both operations with the
existing revision and update semantics.

### Gate 5: refined evidence matroids

Introduce source or reliability labels and test whether a finer matroid can
project conservatively to the two-channel matroid while preserving meaningful
independent corroboration within one polarity.

## Falsification criterion

The matroid analogy should be abandoned at any proposed finer level if the
chosen epistemic closure fails exchange and no independently motivated change
of ground elements or closure semantics restores it. Exchange is treated as a
substantive structural constraint, not as terminology to be imposed by fiat.
