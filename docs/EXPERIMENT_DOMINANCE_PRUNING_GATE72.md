# Gate 72: Experiment Dominance and Pruning

At the unresolved fragile/robust alias, the stress probe has at least as much Bellman Q-value as both legacy status sensors at the first two lookahead depths.

Gate 72 therefore defines a pruned controller containing only:

```text
stop
stressProbe
```

and verifies that this pruning preserves the full Gate-69 Bellman value for one- and two-sample planning.

## Interpretation

More available actions are not automatically epistemically better. Once an experiment is locally dominated, it can be removed without sacrificing rational performance. The controller can therefore carry a proof of irrelevance, not merely a heuristic ranking.

## Boundary

This is local dominance at the alias witness, not a general Blackwell ordering of experiments over every belief state.
