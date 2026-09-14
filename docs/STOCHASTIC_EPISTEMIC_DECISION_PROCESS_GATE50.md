# Gate 50 — Stochastic Epistemic Decision Process

Gate 50 adds an exact finite transition-weight kernel on top of Gate 49. Transition uncertainty is represented by non-negative natural weights over a common positive denominator with an explicit normalization proof.

The crucial modeling separation is deliberate: these transition weights describe uncertainty over the *next epistemic state* after an action. They are not identified with the probability measure stored inside a 4PEL model.

The witness compares `exploit` and `explore` from the same initial state. Exploitation deterministically reaches the recovered-but-fragile basin. Exploration has two equally weighted outcomes, robust Recovery or failure. Under the declared utility, exploration nevertheless has the larger exact expected-utility numerator.

Verified core claims:

- `gate50_explore_has_two_outcomes`
- `gate50_exploit_is_certain_fragile`
- `gate50_transition_kernel_normalized`
- `gate50_exploit_expected_numerator`
- `gate50_explore_expected_numerator`
- `gate50_stochastic_exploration_can_dominate`

This gate adds stochastic control but not reinforcement learning, unknown transition learning, or convergence claims.
