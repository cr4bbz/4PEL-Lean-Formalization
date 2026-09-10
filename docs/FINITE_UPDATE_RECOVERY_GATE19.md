# Gate 19: recovery along finite update sequences

## Research question

Under which necessary and sufficient conditions does compositional classical
recovery remain present, first fail, or later return along a finite sequence of
admissible conditionalizations?

## Dependent update traces

An ordinary list of evidence formulas is insufficient: admissibility of the
second formula must be proved in the model produced by the first update, and so
on. `FiniteConditionalizationTrace` therefore indexes every tail by its actual
strong posterior model. Probability integrity is preserved and carried through
the complete trace.

## Exact preservation theorem

For a formula recovered in the initial model, Lean proves:

```text
RecoveryPreservedAlong phi trace
iff
NoDirectionalGapAlong phi trace.
```

The left side requires compositional recovery at every posterior state. The
right side requires the Gate-12 no-directed-gap condition at every update edge.
This is necessary and sufficient, not merely a sufficient robustness test.

## First loss

`HasFirstDirectionalGap` searches the trace in temporal order. It either marks
the current edge as the first violation or records that the current edge is
safe and continues into the tail. Lean proves:

```text
not RecoveryPreservedAlong phi trace
iff
HasFirstDirectionalGap phi trace
```

when the initial state is recovered. Thus a finite failure cannot remain an
unlocalized global fact: it has an earliest transition and that transition has
the directed threshold explanation from Gate 12.

## Recovery return

Preservation and return are different questions. Once recovery has failed, the
one-step preservation theorem cannot be reused as though its prior-recovery
hypothesis still held.

`RecoveryReturnCondition` instead asks for two facts on an edge:

1. compositional recovery is absent in its source model;
2. recursive semantic classicality holds throughout its strong target model.

Posterior probability integrity makes this condition exactly equivalent to a
genuine transition from non-recovery back to recovery. The equivalence is
lifted to arbitrary finite traces by
`hasRecoveryReturn_iff_hasRecoveryReturnCondition`.

## Finite loss-and-return witness

The four-world witness uses initial weights

```text
a = 3/10, b = 4/10, c = 2/10, d = 1/10
```

and threshold `2/3`. Proposition `p` is true at `a,b`; evidence `q` selects
`a,c`; later evidence `r` selects `a` alone. Hence:

```text
initially:       P(p) = 7/10  -> B(p) = T
after q:         P(p | q) = 3/5 -> B(p) = N
after q, then r: P(p | q,r) = 1 -> B(p) = T.
```

Lean verifies the complete global profile, both admissibility proofs, initial
and final recovery, intermediate non-recovery, the first directional gap, and
the later recovery return. Therefore final recovery does not imply uninterrupted
recovery.

## Scope boundary

Gate 19 covers finite sequences of probability-only conditionalizations. It
does not yet classify product updates, continuous-time paths, infinite update
runs, or give a formula-independent bound on how many recovery changes can
occur.

## Verification

```powershell
lake build
lake env lean PEL4/FiniteUpdateRecoveryAxiomAudit.lean
```
