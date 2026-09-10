# Gate 18: independent classical modal calculus and soundness

## Research question

Can the independent Boolean semantics from Gate 16 be equipped with its own
proof calculus whose derivations are sound, and can those derivations then be
transported back to the recovered 4-PEL sector?

## Implemented calculus

`PEL4/ClassicalModalCalculus.lean` defines the type
`ClassicalModalDerives`. Its rules include:

- identity and cut;
- double-negation introduction and elimination;
- conjunction introduction and elimination;
- disjunction introduction;
- excluded middle and explosion;
- modus ponens and contraposition;
- monotonicity for knowledge, raw possibility, and threshold belief.

The semantic target is not Gate 8's induced split evaluator. It is the separate
Boolean `ClassicalModalModel` introduced in Gate 16.

## Main soundness theorem

Lean proves:

```text
ClassicalModalDerives phi psi
->
StrongClassicalModalSemanticEntails phi psi.
```

The semantic relation quantifies over independent classical models satisfying
`ClassicalModelProbabilityIntegrity`. This condition is essential for the
belief-monotonicity rule: pointwise implication makes the positive event of
the premise a subset of that of the conclusion, and measure monotonicity then
preserves threshold acceptance.

## Transfer to recovered 4-PEL

Combining Gate 18 with Gate 17 gives:

```text
classical derivation
+ probability-integrity 4-PEL model
+ recursive classicality of premise and conclusion
-> recovered 4-PEL LP consequence
-> recovered 4-PEL ST consequence.
```

Thus the classical calculus is not merely sound in isolation: its derivations
can be used safely inside the formally identified classical sector of 4-PEL.

## New boundary witness

`gate18WeakBeliefModel` satisfies the old model fields `mu_total` and
`mu_empty`, but its set function is deliberately nonmonotone. Although
`p -> p or q` is propositionally derivable, the model verifies:

```text
B(p) = true
B(p or q) = false.
```

Consequently belief monotonicity fails over the weak model class. This explains
why the Gate-18 soundness target must quantify over the strong probability
contract rather than silently treating every legacy `Model` as a probability
space.

## What Gate 18 does not prove

Gate 18 establishes soundness only. It does not establish:

- semantic completeness of `ClassicalModalDerives`;
- a canonical-model construction;
- decidability or proof search;
- normalization or cut elimination;
- unrestricted transport into non-recovered 4-PEL.

## Recommended next research step

The soundness-first Gate 18 is complete. Before attempting completeness, the
calculus should be assessed for expressive adequacy—especially whether the
single-premise presentation should become a finite-context sequent system and
which axioms should govern threshold belief. The previously scheduled finite
update-sequence gate can now proceed independently of that larger proof-theory
program.

## Verification

```powershell
lake build
lake env lean PEL4/ClassicalModalCalculusAxiomAudit.lean
```

