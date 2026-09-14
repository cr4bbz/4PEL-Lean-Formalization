# Gate 69: Sequential Bayesian Experiment Design with Sensing Cost

## Aim

Gate 68 selected experiments from the current posterior but used an externally declared stopping threshold. Gate 69 makes stopping endogenous to a finite-horizon optimization problem.

At belief `b`, the controller may either:

1. stop immediately and receive current identification utility `U_stop(b)`, or
2. pay the sensing cost `c(e)` for experiment `e`, observe `o`, update to `b^{e,o}`, and continue optimally.

The Bellman recursion is

```text
V_0(b) = U_stop(b)
V_{n+1}(b) = max(U_stop(b), max_e Q_n(b,e))
Q_n(b,e) = -c(e) + sum_o P(o | e,b) V_n(b^{e,o}).
```

The concrete witness uses Gate 68 identification confidence as `U_stop` and the Gate 67 experiment family.

## Declared sensing costs

```text
statusCheap   : 1/20
statusPrecise : 1/10
stressProbe   : 1/5
```

The stress probe is therefore deliberately the most expensive experiment.

## Initial aliased belief

At the symmetric fragile/robust alias,

```text
stop now = 1/2.
```

With one sample available,

```text
Q(statusCheap)   = 9/20
Q(statusPrecise) = 2/5
Q(stressProbe)   = 7/10.
```

Thus the costly alias-breaking probe has positive net value and strictly dominates stopping and both cheaper status sensors.

With two samples available, the first-step values are

```text
Q(statusCheap)   = 13/20
Q(statusPrecise) = 3/5
Q(stressProbe)   = 7/10.
```

So buying cheap but structurally uninformative evidence first is still strictly worse than probing immediately. The difference is a genuine delay cost.

## After the stress probe

Either possible stress outcome produces identification confidence `9/10`. At that posterior,

```text
stop now         = 9/10
Q(statusCheap)   = 17/20
Q(statusPrecise) = 4/5
Q(stressProbe)   = 7/10.
```

Therefore every additional sample is worth less than stopping. The policy stops because sensing is no longer worth its price, not because a confidence threshold was hard-coded.

## Main result

`gate69_sequential_bayesian_experiment_design_with_cost` verifies that:

- the aliased prior has stop utility `1/2`;
- the two-sample Bellman value is `7/10`;
- the optimal first decision is `sample stressProbe`;
- delaying with `statusCheap` is strictly worse than probing immediately;
- either stress outcome raises stop utility to `9/10`;
- the next optimal decision after either stress outcome is `stop`.

## Interpretation

Gate 69 upgrades adaptive sensing into finite sequential experimental design. The agent now decides both **what to measure** and **when further measurement is no longer worth its cost**.

The strongest conceptual distinction is:

```text
confidence threshold  !=  optimal stopping rule.
```

Gate 68 used the former. Gate 69 derives the latter from an explicit utility-cost tradeoff.

## Boundary

The sensing costs are declared model inputs, not empirically derived quantities. Identification confidence remains the chosen epistemic utility. The result is finite-horizon and assumes fixed known likelihoods. No infinite-horizon convergence, entropy criterion, unknown-model learning, or general theorem about all cost schedules is claimed.
