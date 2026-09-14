# Gate 70: Parametric Sensing-Cost Phase Transition

Gate 69 used the concrete stress-probe price `1/5`. Gate 70 makes that price symbolic.

At the unresolved fragile/robust alias:

```text
gross stress-probe value = 9/10
stop now                 = 1/2
net stress value          = 9/10 - c
```

Therefore sampling is strictly better exactly when

```text
9/10 - c > 1/2
iff
c < 2/5.
```

The controller uses stop-on-ties, so the phase law is:

```text
c < 2/5   -> sample stressProbe
c >= 2/5  -> stop
```

The concrete Gate-69 cost `1/5` lies in the sampling phase and reproduces the verified Q-value `7/10`.

## Interpretation

This is the first symbolic policy boundary in the sequential-sensing program. The value of information is no longer represented only by a few chosen prices: the formalization identifies the exact price at which inquiry ceases to be worth buying.

## Boundary

The threshold is specific to the Gate-67 alias witness and Gate-68 identification utility. Horizon dependence and general stopping-region geometry are deferred to Gate 71.
