# Gate 39 — Epistemic State Sufficiency

## Question

Gate 33 established history-sensitive behavior: opposite orders of the same syntactic evidence ingredients can lead to different Recovery outcomes when earlier updates change the extensional meaning of later belief-dependent evidence.

Gate 39 asks whether this means the update dynamics needs a hidden history register in addition to the current 4PEL model.

For Conditionalization, the answer is no.

## Arbitrary schedule executions

`ConditionalizationScheduleRun` represents a finite admissible sequence of updates by arbitrary evidence formulas. Unlike the Gate-38 static fragment, formulas may contain `bel` and may therefore be semantically update-sensitive.

Each constructor stores exactly the admissibility proof needed at the current model.

## Determinism from the present state

The central theorem is

```text
same current model
+ same future syntactic evidence schedule
=> same final full Model
```

formally `conditionalizationScheduleRun_deterministic` and its state-sufficiency form `same_present_same_future`.

The proof uses proof irrelevance for admissibility witnesses. Two proofs that the same update is admissible cannot encode different hidden dynamics. Once the current model and next evidence formula are fixed, the next model is fixed; induction gives the full finite schedule result.

This statement includes belief-dependent evidence. No belief-free or extension-stability assumption is required.

## Merging histories

Two different past schedules may lead to the same current model. `EpistemicHistoriesMergeAt` records this exact state equality. The theorem `merged_histories_common_future_coalesces` proves that every common admissible future schedule then has exactly the same endpoint.

Thus the current model is a sufficient statistic for represented Conditionalization dynamics:

```text
different histories may matter
only through differences they leave in the present Model.
```

## Relation to Gate 33

Gate 33 does not violate state sufficiency. The intermediate models reached by

```text
B p first
```

and

```text
e first
```

are provably different. At world `b`, the first has `B p = T`, while the second has `B p = N`.

The subsequent divergence is therefore explained by ordinary state dependence:

```text
history -> different present state -> different interpretation of later evidence -> different endpoint.
```

No additional memory variable is needed.

## Markov reading

Within this formal update rule, Conditionalization is history-sensitive but Markov/state-sufficient. History is compressed into the current full epistemic model.

This is stronger than a Recovery-level claim because endpoint model equality yields agreement on every future modal value and every derived compositional Recovery judgment.

The qualification “full model” matters. A coarser observable summary, such as current Recovery status alone, is not sufficient. Gates 29 and 33 already show that equal coarse phases can hide dynamically relevant differences.
