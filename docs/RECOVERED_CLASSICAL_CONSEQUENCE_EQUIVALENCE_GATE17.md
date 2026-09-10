# Gate 17: recovered classical consequence equivalence

## Research question

On the maximal recursive classical fragment, does 4-PEL preserve and reflect
truth and agree with the independent classical consequence relation?

## Result

Yes, with the recovery scope made explicit.
`PEL4/RecoveredClassicalConsequenceEquivalence.lean` proves at recovered nodes:

```text
classical true  iff 4-PEL value T
classical false iff 4-PEL value F.
```

For two globally compositionally classical formulas in one model:

```text
ModalLP_SemanticEntailsIn m phi psi
iff
ClassicalModalSemanticEntailsIn (classicalProjection m) phi psi.
```

With probability integrity, recovered ST and LP consequence coincide as well,
so all three consequence readings agree on this sector. The converse model map
is also tested: embedding an independent classical model and projecting it back
preserves its Boolean evaluation, and the guarded LP consequence of the
embedding agrees with independent classical consequence.

## Exact scope of “conservative equivalence”

This is a semantic, model-relative preservation-and-reflection theorem for
formulas satisfying recursive recovery. It is not:

- an unrestricted collapse of all 4-PEL models;
- a soundness/completeness theorem for an independent proof calculus;
- a proof that LEM and EFQ alone uniquely identify classical logic among all
  possible logical systems.

Those proof-theoretic questions are reserved for Gate 18.

## Verification

```powershell
lake build PEL4.RecoveredClassicalConsequenceEquivalence
lake env lean PEL4/RecoveredClassicalConsequenceEquivalenceAxiomAudit.lean
```

## Next decision gate

Before Gate 18 begins, choose whether its primary target is:

1. a classical proof calculus with soundness only;
2. soundness plus semantic completeness;
3. a stronger decidability/canonical-model package.

Finite update sequences follow that decision rather than preceding it.

