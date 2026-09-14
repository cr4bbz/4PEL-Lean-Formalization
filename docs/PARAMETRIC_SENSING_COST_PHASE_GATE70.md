# Gate 70: Parametric Sensing-Cost Phase Transition

Gate 69 used the concrete stress-probe price `1/5`. Gate 70 exposes the cost transition on an exact hundredth-price grid while separately checking the corresponding rational indifference point.

At the unresolved fragile/robust alias:

```text
gross stress-probe value = 9/10
stop now                 = 1/2
net stress value          = 9/10 - c
```

The rational indifference price is therefore

```text
9/10 - c = 1/2
c = 2/5 = 40/100.
```

The executable controller encodes cost in hundredths and uses stop-on-ties:

```text
cost < 40  -> sample stressProbe
cost >= 40 -> stop
```

Lean additionally verifies the boundary probes `39 -> sample`, `40 -> stop`, `41 -> stop`, the exact rational equality at `2/5`, and that the Gate-69 cost `1/5 = 20/100` lies in the sampling phase and reproduces Q-value `7/10`.

## Interpretation

This is the first policy phase boundary in the sequential-sensing program. Inquiry has an explicit price at which its net value disappears. The controller therefore does not implement unconditional curiosity: it buys information only while the information is worth more than its sensing cost.

## Boundary

The universal executable classification is over an exact hundredth-price grid. The rational boundary equality at `2/5` is verified separately. The threshold is specific to the Gate-67 alias witness and Gate-68 identification utility; no claim is made that every belief or planning horizon has the same scalar boundary.
