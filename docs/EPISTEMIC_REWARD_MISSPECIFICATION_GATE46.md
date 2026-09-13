# Gate 46 — Epistemic Reward Misspecification / Information Avoidance

## Research question

Can a formally rational one-step agent, given the active acquisition choices from Gate 45, prefer information that preserves immediate Recovery and reject an available acquisition plan that disrupts Recovery solely because of a narrow reward specification?

## Setup

Gate 46 extracts a two-action menu from Gate 45:

- `preserve`: actively observe the Recovery-preserving evidence `p`;
- `probe`: actively observe the destabilizing evidence `e`.

Both choices are realized controlled transitions from the same initial DynamicInstability model.

Their known successors differ:

- `preserve` reaches `Gate29RecoveryPreservingUpdated`, which satisfies Compositional Recovery for `B p`;
- `probe` reaches `DynamicInstabilityUpdated`, which does not satisfy Compositional Recovery for `B p`.

Lean also proves the two full successor models are distinct.

## Reward layer

Gate 46 introduces the minimal one-step reward type

```text
State → Action → State → Nat
```

and instantiates a deliberately narrow immediate-Recovery proxy on the binary menu:

```text
preserve ↦ 1
probe    ↦ 0
```

A calibration theorem proves that, on the realized Gate-45 outcomes, the one-point branch is exactly the recovered successor and the zero-point branch is exactly the non-recovered successor.

## Myopic optimality

`Gate46MyopicallyOptimal choice` means that the choice's immediate reward is at least as large as every alternative in the two-action menu.

Verified results:

- `preserve` is myopically optimal;
- `probe` is not myopically optimal;
- every myopically optimal choice is therefore exactly `preserve`.

Thus a reward-maximizing one-step controller avoids the Recovery-disrupting acquisition option, despite that option being available from the same epistemic state.

The main theorem is:

```text
gate46_naive_recovery_reward_selects_information_avoidance
```

## Interpretation

Gate 46 is the first verified reward-design result in the project. It formalizes a local mechanism analogous to confirmation-bias-like information avoidance:

```text
available disruptive evidence
        +
reward only immediate Recovery
        ↓
optimal one-step choice preserves Recovery instead
```

This is best described as **myopic Recovery-proxy information avoidance**.

## No-overclaim boundary

Gate 46 does **not** prove that the avoided `probe` action is objectively better.

It does not yet provide:

- a truth-directed utility;
- mutual information or another information-theoretic value;
- delayed reward;
- a finite- or infinite-horizon return;
- stochastic outcome probabilities;
- a complete MDP;
- a theorem that the disruptive branch eventually dominates the preserving branch.

Accordingly, `reward misspecification` names the intentionally narrow reward relative to the broader epistemic objectives under investigation. Lean has not yet proved that the proxy conflicts with a formal external truth standard.

## Next gate

Gate 47 should add a temporal objective and construct a **rational destabilization** witness: a case where accepting temporary Non-Recovery yields a strictly better later epistemic outcome than preserving immediate Recovery. That would turn Gate 46's local avoidance mechanism into a genuine long-horizon reward-misspecification result.
