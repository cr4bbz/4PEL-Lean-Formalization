# Gate 71: Stopping-Region Geometry

Gate 71 checks whether the concrete Gate-69 policy changes when the planning horizon grows from one to two available samples.

Verified witness geometry:

```text
unresolved alias, 1-step lookahead -> sampling
unresolved alias, 2-step lookahead -> sampling
post-stress posterior, 1-step       -> stopping
post-stress posterior, 2-step       -> stopping
```

The initial Bellman value is `7/10` at both positive horizons already formalized by Gate 69. After either stress outcome, immediate stopping remains optimal.

## Interpretation

The policy is not a fragile artifact of a one-step calculation. The alias and the resolved posterior occupy different local decision regions that survive the first increase in planning depth.

## Boundary

No global monotonicity theorem for arbitrary sequential models is claimed. The Gate-69 structure deliberately does not encode all probability-normalization and regularity hypotheses that such a theorem would need.
