# Gate 15: maximal recursive classical-law fragment

## Research question

Is `CompositionallyClassicalAt` the largest subformula- and
accessibility-recursive fragment on which tolerant LEM and universal EFQ hold
at every relevant node?

## Result

Yes, relative to the explicitly declared comparison class. A candidate
fragment is `IsRecursiveClassicalLawFragment` when every formula node it admits
satisfies the complete Gate-14 traversal. Lean proves:

```text
every recursively law-closed candidate
is contained in CompositionallyClassicalAt.
```

This is the precise sense in which the recovery sector is maximal. No claim is
made about unrelated languages, alternative connectives, proof calculi, or
weaker closure notions.

## Necessity witnesses

The finite model `gate15LawBoundaryModel` verifies three boundaries:

- a gap `N` fails LEM but satisfies EFQ;
- a glut `B` satisfies LEM but fails EFQ;
- a conjunction can have classical root value `F` while hiding a gappy
  subformula.

Therefore neither law axis can be omitted, and testing only the root formula is
strictly weaker than recursive recovery.

## Verification

```powershell
lake build PEL4.MaximalClassicalLawFragment
lake env lean PEL4/MaximalClassicalLawFragmentAxiomAudit.lean
```

