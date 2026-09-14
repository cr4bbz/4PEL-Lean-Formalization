# Gate 59 — Canonical Epistemic Beliefs

## Question

Should two different list encodings count as different epistemic states when they assign the same total probability to every hidden state?

## Verified result

`PEL4.CanonicalEpistemicBeliefs` defines aggregate state weight
`bayesianWeightAt` and extensional equivalence:

```text
BayesianBeliefEquivalent b₁ b₂
⇔ ∀ s, bayesianWeightAt b₁ s = bayesianWeightAt b₂ s
```

The relation is reflexive, symmetric and transitive. Splitting or merging mass on the same state preserves the represented belief.

The concrete witness proves that

```text
[(1/2, robust), (1/2, robust)]
```

and

```text
[(1, robust)]
```

are syntactically unequal but extensionally equivalent.

Key theorems:

- `bayesianBelief_split_same_state_equivalent`
- `gate59_duplicate_and_canonical_equivalent`
- `gate59_syntax_not_epistemic_identity`

`canonicalBayesianProfile` records one aggregate coordinate per state in a chosen finite support.

## Boundary

Canonicalization is support-relative and keeps zero coordinates. This gate establishes extensional identity of finite belief states, not quotient types or a general finite-distribution library.
