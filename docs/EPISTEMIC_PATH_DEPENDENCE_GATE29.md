# Gate 29 — Epistemic Path Dependence

## Question

Can one and the same finite-descent system, from one and the same recovered start state, admit two valid infinite futures that stabilize to different Recovery endpoints?

Gate 28 only established that Recovery and Non-Recovery are both possible asymptotic endpoints across different witness systems. Gate 29 strengthens this to genuine branching inside a single transition system and then checks whether the same branching phenomenon already appears in concrete 4PEL Conditionalization.

## Layer 1: minimal same-start asymptotic witness

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

`gate29_same_start_different_endpoints` proves:

`RecoveryPathDependentAt gate29System Gate29State.start`.

The gate also introduces `RobustEventuallyRecoveryAt`. The theorem `gate29_recovery_now_not_robust_future` establishes the strict distinction:

> being recovered now does not imply eventual Recovery along every admissible future.

## Layer 2: concrete 4PEL Conditionalization split

The existing `DynamicInstabilityModel` already supplies a stronger semantic witness.

The starting model is compositionally recovered for `B p`.

From exactly that model, two evidence formulas are admissible:

1. learn `p`: the posterior belief profile remains `T/T/T`, so compositional Recovery is preserved;
2. learn `e`: the already verified instability update produces `T/N/T`, so compositional Recovery is destroyed.

The theorem `gate29_concrete_conditionalization_split` packages this same-model fork:

- shared recovered starting model;
- both updates admissible;
- one successor recovered;
- the other successor non-recovered.

This establishes genuine one-step path dependence for the concrete Conditionalization operator, not merely for the abstract descent contract.

## Interpretation

Gate 29 separates two notions that had previously been easy to conflate:

- `Recovery now`
- `Recovery under all admissible futures`

The former does not imply the latter. A recovered epistemic state can contain a latent branching structure in which different admissible evidence choices lead to different Recovery phases.

## Remaining boundary

The abstract system proves different **eventual** endpoints. The concrete 4PEL model currently proves a different **one-step** Recovery outcome from the same starting model.

What is not yet formalized is an infinite pair of concrete Conditionalization schedules from that model whose eventual Recovery endpoints are proved different. Establishing such schedules would close the remaining gap between the abstract asymptotic theorem and the concrete semantic witness.

Likewise, Gate 29 does not yet establish order-sensitive hysteresis for the same multiset of evidence. That requires a stronger test such as comparing `A;B` with `B;A` from the same start and is intentionally left for a later gate.
