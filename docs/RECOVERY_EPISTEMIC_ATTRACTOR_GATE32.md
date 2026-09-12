# Gate 32: Recovery as Epistemic Attractor

## Question

Gates 27--31 show that Recovery has finite variation, eventually stabilizes, may end in either Boolean phase, can be path-dependent, can be confluent under suitable update-equivalence conditions, and can satisfy explicit stabilization deadlines.

None of those results says that Recovery is the phase toward which learning is directed.

Gate 32 asks:

> Under what learning conditions must the eventual stable endpoint be Recovery rather than Non-Recovery?

## Layer 1: the exact trajectory-level criterion

For a valid infinite `RecoveryDescentSystem` trajectory, define `NonRecoveryTransientAlong` by requiring that every time at which the Recovery status is false has a strictly later time at which it is true.

Formally:

```text
NonRecoveryTransientAlong sys trajectory :=
  forall n,
    status(trajectory n) = false ->
    exists m > n, status(trajectory m) = true
```

Gate 28 already proves that every valid descent trajectory eventually has exactly one stable Boolean endpoint. This turns Non-Recovery transience into an exact criterion:

```text
recoveryTrajectory_eventuallyRecovery_iff_nonRecoveryTransient
```

Hence, on valid finite-descent trajectories,

\[
\boxed{
\text{eventually permanent Recovery}
\iff
\text{every Non-Recovery phase is transient}
}
\]

This is not yet a substantive learning law by itself. It identifies exactly what must be added to the Gate-27/28 stabilization theory to select the Recovery endpoint.

## Layer 2: directional version of the Gate-31 deadline

Gate 31 gives the generic stabilization deadline

\[
N_{\mathrm{stab}} \le B\,\Phi_0
\]

under `BoundedRecoveryProgress` with horizon `B`.

If `NonRecoveryTransientAlong` is added, the stable endpoint cannot be Non-Recovery. Therefore the same numerical bound becomes a Recovery deadline:

```text
recoveryTrajectory_recoveredBy_of_boundedProgress
```

and

\[
\boxed{
\exists N \le B\Phi_0\;\forall n\ge N:\ Recovery(n)
}
\]

Thus Gate 31 bounds when the phase stops changing, while Gate 32 can turn the same bound into a statement about which phase has been reached.

## Layer 3: a local structural attractor contract

The stronger part of Gate 32 introduces two local properties of the update relation.

### Recovery absorption

```text
RecoveryAbsorbing sys
```

means

\[
Recovery(s) \land s\to t \;\Rightarrow\; Recovery(t).
\]

Once Recovery is reached, allowed learning steps cannot destroy it.

### Non-Recovery consumes potential

```text
NonRecoveryConsumesPotential sys
```

means

\[
\neg Recovery(s) \land s\to t
\;\Rightarrow\;
\Phi(t)<\Phi(s).
\]

This is stronger than the original Gate-26 descent contract. Gate 26 only requires strict potential loss when the Boolean Recovery status itself changes. Gate 32 requires every continued learning step in Non-Recovery to consume one or more units of finite potential, even if the Boolean status has not changed yet.

Under these two assumptions, the potential becomes more than a flip budget. It behaves as a finite distance-to-Recovery resource.

## Main attractor theorem

The theorem

```text
recoveryTrajectory_eventuallyRecovery_of_attractorContract
```

proves:

\[
\boxed{
RecoveryAbsorbing
\land
NonRecoveryConsumesPotential
\Rightarrow
\exists N\le\Phi(s_0)\;\forall n\ge N:\ Recovery(s_n)
}
\]

The proof is quantitative. If the trajectory is still in Non-Recovery, each next step strictly decreases the natural-valued potential. A natural number cannot decrease strictly more than its initial value many times. Consequently Recovery must be reached no later than time `Phi(s_0)`. Absorption then makes it permanent.

This is stronger than the Gate-31 bound because no independent stuttering factor `B` is required: the local attractor contract declares Non-Recovery stuttering itself to be progress-consuming.

## Minimal witness

`Gate32State` has only two states:

```text
nonRecovery --recover--> recovery --stayRecovered--> recovery -- ...
```

with potentials

```text
Phi(nonRecovery) = 1
Phi(recovery)    = 0
```

The system satisfies both `RecoveryAbsorbing` and `NonRecoveryConsumesPotential`, and its unique displayed trajectory becomes permanently recovered after one step.

## Why Gate 28's counterexample is excluded

The permanently Non-Recovery system from Gate 28 has status `false`, potential `0`, and allows a self-loop forever. Gate 32 proves:

```text
gate32_gate28_nonRecovery_not_potential_consuming
```

The reason is structural. Its Non-Recovery self-loop would require

\[
0<0,
\]

which is impossible. The new attractor contract therefore excludes exactly the kind of zero-cost permanent Non-Recovery trap that made Gate 28 possible.

## Interpretation

The development now separates three notions that should not be conflated:

1. **finite variation**: Recovery cannot flip infinitely often;
2. **stabilization**: the Recovery status eventually becomes constant;
3. **attraction**: the eventual constant phase is specifically Recovery.

Gates 26--28 establish the first two without the third. Gate 32 gives explicit sufficient conditions for the third.

The conceptual shift is that `Phi` can play two distinct roles:

- under the basic descent contract, it is a budget for Recovery-status changes;
- under the stronger attractor contract, it is a distance-like resource that must be consumed while the system remains outside Recovery.

## Boundary and no-overclaim

Gate 32 does **not** prove that arbitrary 4PEL Conditionalization satisfies the attractor contract.

In fact, the earlier dynamic instability and Gate-29 path-dependence witnesses show that unrestricted admissible evidence schedules can move a recovered model into Non-Recovery. Therefore `RecoveryAbsorbing` is false for arbitrary Conditionalization schedules in general.

The theorem should be read conditionally:

> if a class of learning updates preserves Recovery once reached and strictly consumes a finite non-Recovery resource before Recovery is reached, then Recovery is a quantitative epistemic attractor.

A later task is to identify natural restricted classes of 4PEL learning schedules for which these local assumptions are derivable from the concrete semantics rather than postulated abstractly.

## Gate result

Gate 32 upgrades the phase-dynamics program from a theory of eventual Boolean stabilization to a conditional theory of truth-directed epistemic attraction:

\[
\boxed{
\text{finite descent}
+
\text{Recovery absorption}
+
\text{Non-Recovery progress}
\Longrightarrow
\text{permanent Recovery in finite time}
}
\]
