# Gate 47 — Rational Destabilization through Robust Recovery

## Research question

Can a 4PEL-inspired epistemic controller rationally prefer an action that causes temporary Non-Recovery when a longer-horizon objective rewards robust Recovery rather than only immediate Recovery?

## Construction

Gate 47 introduces a finite temporal witness with six states:

- `start`: initially recovered;
- `fragile`: recovered but vulnerable to an admitted stress test;
- `destabilized`: temporary Non-Recovery after probing;
- `integrating`: continued Non-Recovery while the probe is incorporated;
- `robust`: recovered and stable under the admitted stress test;
- `broken`: failure state reached by stressing the fragile state.

Two trajectories are compared:

```text
preserve: start -> fragile -> fragile -> fragile -> ...
probe:    start -> destabilized -> integrating -> robust -> robust -> ...
```

The preserve trajectory has the better immediate Recovery score. The probe trajectory reaches the only robust terminal state after three steps.

## Robust Recovery

`StressRobustRecovery Recovered Stress s` means:

1. `s` is currently recovered, and
2. every admitted one-step stress successor of `s` is also recovered.

The witness proves:

- `fragile` is recovered;
- `fragile` is not robust, because its stress successor is `broken`;
- `robust` is robust, because its admitted stress successor is itself.

## Preference reversal

The immediate objective reproduces Gate 46:

```text
preserve > probe
```

The three-step objective is lexicographic:

1. terminal robust Recovery is primary;
2. accumulated Recovery is a tie-breaker.

Thus:

```text
immediate horizon: preserve > probe
three-step horizon: probe > preserve
```

The main theorem is:

```lean
gate47_rational_destabilization_preference_reversal
```

It verifies that the disruptive path is locally worse, traverses Non-Recovery, and nevertheless wins under the explicitly declared robust long-horizon objective.

## Relation to previous gates

Gate 41 established that an early turbulent prefix can coexist with later permanent Recovery. Gate 46 established that a naive immediate-Recovery reward rejects a disruptive probe. Gate 47 connects the two ideas: temporal destabilization can be selected rationally when the objective values robustness rather than immediate status alone.

## No-overclaim boundary

Gate 47 does **not** prove that robust Recovery is correspondence truth, that all disruptive evidence is valuable, or that every longer horizon favors probing. The result is an existential structural witness relative to an explicit epistemic objective.

## Next gate

Gate 48 converts the one-shot preference reversal into a repeated exploration–exploitation control problem and asks whether exploration is necessary for reaching the robust region.
