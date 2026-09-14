# Gate 74: Posterior Sample Complexity

Gate 74 reuses the exact Gate-66 learning curve and asks for the first verified repetition count that reaches a confidence target.

```text
prior      = 1/2
1 signal   = 9/10
2 signals  = 81/82
3 signals  = 729/730
```

Within this exact window:

```text
90%   -> 1 sample
98%   -> 2 samples
99%   -> 3 samples
99.9% -> not reached within 3
```

## Interpretation

Evidence quality and evidence quantity are now linked quantitatively. A confidence demand has an epistemic price measured in observations, not only in sensing cost.

## Boundary

This is finite exact sample complexity over the already verified first three updates. It is not yet an asymptotic `n(epsilon)` theorem.
