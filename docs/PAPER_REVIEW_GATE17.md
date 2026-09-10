# Paper review after Gate 17

## Review target

This review compares manuscript version 0.13 with the formal development now
completed through Gate 17. It is a currency and claim-scope review, not an
independent external peer review.

## Overall judgment

The manuscript remains internally defensible: its explicit nonclaims prevent
Gate-8/9 representation results from being overstated as an independent
classical completeness theorem. It is, however, materially behind the Lean
development. The paper ends at Gate 9 while the repository now contains two
complete later chains:

```text
Gates 10--13: compositional and dynamic recovery
Gates 14--17: recursive laws, maximality, independent semantics, equivalence.
```

The next paper revision should integrate these as two grouped arguments rather
than eight disconnected implementation reports.

## Findings by priority

### High: the classical target description is now stale

Sections 20, 21, and the conclusion correctly say that Gate 8 supplies only an
evaluator induced by 4-PEL. Gate 16 does not make that historical statement
false, but it changes the repository-level boundary by adding the separate
`ClassicalModalModel` type and its own Boolean evaluator. A revision must
distinguish:

1. split CPEL representation over the same 4-PEL model (Gate 8);
2. a separate classical modal model type and evaluator (Gate 16);
3. a guarded comparison theorem between them (Gate 17).

### High: two different consequence results must not be conflated

Gate 9 proves ST/LP coincidence from classicality of the antecedent alone. Gate
17 proves agreement with independent classical consequence under recursive
classicality of both antecedent and consequent. The additional consequent guard
is needed because Boolean projection can otherwise lose the negative coordinate
inside negation and modal evaluation.

### High: maximality requires its qualifier

Gate 15 proves greatestness only among predicates required to satisfy the
declared recursive LEM/EFQ traversal. The paper should say “maximal recursive
classical-law fragment relative to this closure notion,” not “the maximal
classical fragment of 4-PEL” without qualification.

### Medium: root-level classicality is too weak

The new finite witness where a classical `F` conjunction masks a gappy atom is
an effective explanation of why Gates 10, 13, and 14 use recursive predicates.
It belongs near the first definition of compositional classicality.

### Medium: Gate 18 remains a real proof-theoretic step

Truth preservation/reflection and semantic consequence equivalence do not yet
supply an independent calculus, soundness/completeness, a canonical model, or
decidability. Existing manuscript nonclaims should remain until Gate 18 chooses
and proves one of those targets.

## Recommended version-0.14 structure

1. Add one section for Gates 10--13: recursive recovery, update fracture and
   restoration, directional gaps, and preservation of probability integrity.
2. Add one section for Gates 14--15: the recursive LEM/EFQ characterization,
   qualified maximality, and the three finite boundary witnesses.
3. Add one section for Gates 16--17: independent classical model semantics,
   projection/embedding, truth preservation/reflection, and guarded consequence
   equivalence.
4. Update the mechanization branch, module list, build count, and focused audit
   commands.
5. Update the conclusion so that “no independent target semantics” becomes “no
   independent proof calculus or completeness theorem.”
6. Retain the unrestricted glut countermodel so the reader cannot mistake the
   recovered equivalence for a global collapse.

## Layout and build check

The existing manuscript was rendered after the repository update:

```text
version 0.13
54 pages
committed normalized PDF text matches the fresh render.
```

No TeX section was added during this review. Integrating Gates 10--17 should be
a deliberate manuscript version increment with a new render and visual pass,
not a silent documentation edit.

## Gate-18 editorial decision

The manuscript can publish the Gate-17 semantic result without Gate 18 if it is
presented as a guarded conservativity theorem. If Gate 18 is attempted before
the next paper version, the preferred minimum publishable target is an
independent classical calculus with soundness; completeness should be claimed
only if a model construction is actually formalized.

