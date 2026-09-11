# Gate 29 — Epistemic Path Dependence

## Question

Can one and the same recovered epistemic start state admit different admissible futures that stabilize to different Recovery endpoints?

Gate 28 established only that Recovery and Non-Recovery are both possible asymptotic endpoints across different witness systems. Gate 29 strengthens this twice: first to genuine branching inside one abstract finite-descent system, then to concrete infinite Conditionalization schedules from one fixed 4PEL model.

## Layer 1: minimal same-start asymptotic witness

The abstract state space has three states:

- `start`: Recovery, potential 1
- `recovery`: Recovery, potential 1
- `nonRecovery`: Non-Recovery, potential 0

The admissible transitions are:

- `start -> recovery`
- `start -> nonRecovery`
- `recovery -> recovery`
- `nonRecovery -> nonRecovery`

The first branch preserves status and spends no resource. The second branch changes status once and consumes the single available unit of potential. Both satisfy the Gate-26 one-step descent contract.

Thus two valid trajectories share the same initial state:

`start -> recovery -> recovery -> ...`

and

`start -> nonRecovery -> nonRecovery -> ...`

The first is eventually always Recovery, the second eventually always Non-Recovery.

`gate29_same_start_different_endpoints` proves:

`RecoveryPathDependentAt gate29System Gate29State.start`.

The gate also introduces `RobustEventuallyRecoveryAt`. The theorem `gate29_recovery_now_not_robust_future` establishes the strict distinction:

> being recovered now does not imply eventual Recovery along every admissible future.

## Layer 2: concrete one-step 4PEL split

The existing `DynamicInstabilityModel` supplies the semantic start state. It is compositionally recovered for `B p`.

From exactly that model, two atomic evidence formulas are admissible:

1. learn `p`: the posterior belief profile remains `T/T/T`, so compositional Recovery is preserved;
2. learn `e`: the verified instability update produces `T/N/T`, so compositional Recovery is destroyed.

The theorem `gate29_concrete_conditionalization_split` packages this same-model fork:

- shared recovered starting model;
- both updates admissible;
- one successor recovered;
- the other successor non-recovered.

This already establishes genuine one-step path dependence for the concrete Conditionalization operator.

## Layer 3: atomic Conditionalization is idempotent

To turn the one-step split into a result about infinite concrete schedules, Gate 29 proves a general auxiliary theorem for admissible atomic evidence.

For an atom `a`, once a model has been conditioned on `a`, the positive event for `a` is unchanged and has posterior mass one. Intersecting an arbitrary query set with that event again does not change its posterior mass. Therefore:

`conditionalize_repeat_prop_eq`

proves, up to proof irrelevance of the model's normalization witnesses,

`C_a(C_a(M)) = C_a(M)`.

The proof is decomposed into event invariance, event mass one, posterior-measure idempotence, repeated admissibility, equality of the probability functions, and finally full model equality.

This is stronger than merely showing Recovery stutters: the entire 4PEL model is a fixed point of repeated conditioning on the same admissible atomic evidence after the first update.

## Layer 4: concrete infinite schedules

Gate 29 introduces `RepeatedAtomicConditionalizationFollows`, requiring every successor in an infinite trajectory to be obtained by an admissible Conditionalization on one fixed atom.

Two concrete trajectories start from the identical `DynamicInstabilityModel`:

`M0 -> C_p(M0) -> C_p(M0) -> C_p(M0) -> ...`

and

`M0 -> C_e(M0) -> C_e(M0) -> C_e(M0) -> ...`.

The idempotence theorem verifies that both are genuine infinite update schedules rather than manually frozen sequences.

The Recovery endpoint is then immediate from index one:

- the `p` trajectory is compositionally recovered forever;
- the `e` trajectory is compositionally non-recovered forever.

The main theorem `gate29_concrete_asymptotic_path_dependence` packages:

- identical concrete start model;
- admissibility at every step of both infinite schedules;
- eventual permanent Recovery on the `p` branch;
- eventual permanent Non-Recovery on the `e` branch.

Hence Gate 29 establishes:

`same concrete recovered 4PEL state + different admissible evidence schedules -> different asymptotic Recovery phases`.

## Interpretation

Gate 29 now separates three claims:

- `Recovery now`
- `eventual Recovery along one admissible future`
- `Recovery under all admissible futures`

The first does not imply the third. Recovery is therefore a present-state property, not by itself a guarantee about the phase selected by future evidence.

In the concrete witness the history dependence is especially sharp: the first evidence choice sends the system into one of two different Conditionalization fixed points. After that choice, repeating the same evidence cannot repair or undo the selected Recovery phase.

## Remaining boundary

Gate 29 proves path dependence under **different evidence schedules**. It does not yet prove order-sensitive hysteresis for the same collection of evidence. A stronger future test would compare, for example, `A;B` with `B;A` from the same start and ask whether the final model or final Recovery phase differs.

That distinction matters: Gate 29 proves branching dependence on which admissible path is taken, but not yet dependence on order when informational content is otherwise held fixed. The latter remains appropriate for the later hysteresis program rather than being smuggled into the present result.
