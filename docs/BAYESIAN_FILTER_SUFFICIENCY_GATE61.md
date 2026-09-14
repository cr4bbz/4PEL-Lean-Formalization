# Gate 61 — Bayesian Filter Sufficiency

## Question

Once the current Bayesian posterior is known, must the controller retain the full observation/action history that produced it?

## Verified result

`PEL4.BayesianFilterSufficiency` defines finite noisy filter runs over future `(action, observation)` inputs.

The central filtering theorem is:

```text
same current posterior + same future inputs
⇒ same future posterior
```

and, equivalently, if two arbitrary histories merge into the same current posterior, every common future input schedule produces the same posterior endpoint.

Key theorems:

- `noisyBayesianFilter_same_present_same_future`
- `noisyBayesianFilter_merged_histories_common_future`
- `gate61_history_compression_witness`
- `gate61_bayesian_posterior_is_markov_sufficient`

Gate 59 is integrated through `canonicalBayesianProfile_eq_of_equivalent`: extensionally equivalent list beliefs induce the same canonical controller state on a fixed finite support.

This is the partially observable analogue of Gate 39's full-model state-sufficiency result.

## Boundary

The theorem assumes a fixed hidden transition model, fixed noisy observation kernel, and the received future observations. It proves filtering sufficiency, not truth identification, optimal control, robustness to model misspecification, or statistical consistency.
