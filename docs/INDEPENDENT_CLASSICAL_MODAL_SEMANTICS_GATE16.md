# Gate 16: independent classical modal semantics

## Research question

Can 4-PEL be compared with a genuinely separate two-valued
probabilistic-epistemic semantics instead of only with the induced two-channel
CPEL evaluator from Gate 8?

## Result

`PEL4/IndependentClassicalModalSemantics.lean` introduces the separate structure
`ClassicalModalModel`. Atomic and formula values are Boolean. Its evaluator
uses:

- Boolean negation and conjunction;
- positive-event Lockean threshold belief;
- ordinary universal accessibility for knowledge;
- ordinary existential accessibility for possibility.

The type is not an alias for `Model` and stores no negative support channel.
Two explicit comparison maps are supplied:

```text
Model.classicalProjection
ClassicalModalModel.fdeEmbedding.
```

Both preserve the strong finite-probability integrity contract. On the maximal
recursive classical fragment, Lean proves preservation of the positive truth
coordinate and full reconstruction:

```text
evalClassicalModal (classicalProjection m) w phi
= (evalModal m w phi).pos

evalModal m w phi
= ofClassicalBool (evalClassicalModal (classicalProjection m) w phi).
```

## Boundary

Outside recovery, the projection is intentionally lossy: `N` and `F` share a
false positive bit, while `T` and `B` share a true positive bit. Standard
classical knowledge and four-valued evidence-stable knowledge also need not
agree on nonclassical profiles. Gate 16 therefore does not claim unrestricted
equivalence or completeness.

## Verification

```powershell
lake build PEL4.IndependentClassicalModalSemantics
lake env lean PEL4/IndependentClassicalModalSemanticsAxiomAudit.lean
```

