# Gate 36 — Semantic Feedback Boundary

## Question

Gate 33 established epistemic hysteresis with the same syntactic evidence ingredients `{e, B p}`. The mechanism was not ordinary Bayesian noncommutativity. The first update changed the positive extension denoted by the later belief-evidence formula.

Gate 36 asks which evidence formulas are guaranteed not to behave that way.

## Belief-free evidence

For the evidence syntax

```text
prop | not | and | bel
```

Gate 36 defines `Formula.BeliefFree` recursively. Atomic formulas and Boolean compounds of atomic formulas are belief-free; every `bel` node lies outside the fragment.

Conditionalization changes only the model's probability measure. Accessibility and atomic valuation remain fixed. Structural induction therefore proves

```text
BeliefFree(phi)
  -> eval (conditionalize M E) w phi = eval M w phi
```

for every world `w` and every admissible update `E`.

Because the conditioning event is obtained by filtering the unchanged accessibility list using the positive bit of `eval`, the entire positive evidence event is invariant:

```text
BeliefFree(phi)
  -> ExtensionStableUnder(M, E, phi).
```

This is exact list equality, not merely equality of probability mass.

## Gate-33 counter-side

The Gate-33 evidence `B p` is not belief-free. In the instability model,

```text
before e:  [[B p]]+ = {a,b,c}
after e:   [[B p]]+ = {a,c}
```

so it is an explicit witness of `EvidenceExtensionSensitiveUnder`.

Thus the verified boundary is

```text
belief-free evidence -> extension stability guaranteed
belief evidence       -> extension sensitivity possible
```

The converse is deliberately not claimed. A formula can contain `bel` and still be extension-stable in a particular model or under a particular update.

## Consequence for the Gate-33 diagnosis

The Hysteresis witness depends on semantic feedback. It cannot be reproduced by a belief-free evidence formula through the same mechanism because the extensional content of such evidence cannot be changed by prior probability-only conditionalization.

This prepares Gate 38. Once evidence extensions are static, one can ask when arbitrary finite schedules admit permutation/duplication normal forms analogous to the atomic commutative-idempotent subdynamics already established in Gates 29 and 30.
