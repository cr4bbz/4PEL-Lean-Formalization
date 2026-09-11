# Gate 29 — Epistemic Path Dependence

## Question

Can one and the same finite-descent system, from one and the same recovered start state, admit two valid infinite futures that stabilize to different Recovery endpoints?

Gate 28 only established that Recovery and Non-Recovery are both possible asymptotic endpoints across different witness systems. Gate 29 strengthens this to genuine branching inside a single transition system.

## Minimal witness

The state space has three states:

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

## Formal result

`gate29_same_start_different_endpoints` proves `RecoveryPathDependentAt gate29System Gate29State.start`.

The gate also introduces `RobustEventuallyRecoveryAt`. The theorem `gate29_recovery_now_not_robust_future` establishes the strict distinction:

> being recovered now does not imply eventual Recovery along every admissible future.

This is the first precise dynamic separation between current Recovery and future-robust Recovery in the Gate-26/27/28 framework.

## What this does not yet prove

This witness is abstract. It shows that the finite-descent contract permits path dependence. It does **not** yet show that concrete 4PEL Conditionalization from one fixed model and formula realizes different eventual endpoints under two admissible evidence schedules.

That concrete semantic question is the next subgoal of Gate 29. Until such a witness is found, terms such as “epistemic hysteresis” should remain interpretive hypotheses rather than established properties of Conditionalization.
