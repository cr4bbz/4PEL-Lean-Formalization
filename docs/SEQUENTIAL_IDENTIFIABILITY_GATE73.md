# Gate 73: Sequential Identifiability

Gate 73 separates one-shot from sequential identifiability with a four-state, two-bit witness.

```text
firstBit alone  -> not identifying
secondBit alone -> not identifying
[firstBit, secondBit] -> identifying
[secondBit, firstBit] -> identifying
```

The two-step plan assigns the distinct signatures `00`, `01`, `10`, and `11` to the four hidden states.

## Interpretation

Failure of one measurement to identify the world does not imply that the world is unidentifiable. Distinct weak experiments can compose into a complete identifying code. The epistemic resource is therefore not only sensor precision, but experimental diversity.

## Boundary

This witness is deterministic and finite. Quantitative stochastic learning rates are deferred to Gate 74.
