# Gate 57 — Normalized Bayesian Belief-State MDP

## Question

Can the finite epistemic POMDP from Gate 56 be lifted to an exact normalized
Bayesian belief-state process, so that hidden-state partial observability becomes
full observability over posterior beliefs?

## Construction

Gate 57 introduces exact rational beliefs over hidden epistemic states:

```lean
abbrev BayesianEpistemicBelief (State : Type) := List (Rat × State)
```

The update is split into the standard Bayesian stages:

1. **prediction** through the hidden stochastic transition kernel;
2. **conditioning** on the received observation;
3. **normalization** by the surviving observation mass.

The transition probabilities used here are the Gate-50/56 stochastic weights
divided by their common denominator. They remain mathematically separate from
probability measures internal to a 4PEL epistemic model.

## Belief-state MDP

`FiniteBayesianBeliefStateMDP` packages the hidden-state POMDP with a finite
observation alphabet. `bayesianBeliefMDPOutcomes` maps one fully observed belief
and one action to observation-indexed posterior branches:

```text
belief --action--> [(Pr(o1), posterior(o1)), ..., (Pr(on), posterior(on))]
```

Thus the controller's state is now the posterior belief itself.

## Finite witness

The aliased prior is

```text
P(fragile) = 1/2
P(robust)  = 1/2
```

Both states currently emit the same coarse `recovery` observation. After the
`explore` action, prediction gives

```text
P(destabilized) = 1/2
P(robust)       = 1/2.
```

The next observation then separates the alternatives:

```text
recovery    => posterior robust = 1
nonRecovery => posterior destabilized = 1.
```

The induced belief-state transition is therefore exactly

```text
1/2 -> [robust with probability 1]
1/2 -> [destabilized with probability 1].
```

The two branch probabilities sum to one.

## Truth-calibration bridge

Gate 54 remains external to the probabilistic machinery. When the Recovery
observation yields the point posterior on `robust`, that hidden state is already
verified to have zero calibration error and to satisfy the explicit
`TruthAligned` criterion. Bayesian normalization does not redefine truth; it
only propagates uncertainty over states for which the truth/calibration bridge
was separately supplied.

## Verified boundary

Gate 57 does **not** yet establish:

- generic canonical aggregation of duplicate hidden states;
- a noisy observation kernel;
- generic normalization theorems for arbitrary list beliefs;
- continuous belief spaces;
- policy optimization or RL convergence.

The verified result is narrower: for the finite Gate-56 witness, the epistemic
POMDP induces an exact normalized Markov process over Bayesian beliefs.

## Next gate

A natural Gate 58 is a noisy observation channel. That removes the simplifying
assumption that Recovery/Non-Recovery is observed without error and forces the
posterior to remain genuinely uncertain after observations.
