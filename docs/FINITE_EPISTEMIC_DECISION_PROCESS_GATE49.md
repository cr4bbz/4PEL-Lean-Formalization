# Gate 49 — Finite Epistemic Decision Process + Bellman Recursion

Gate 49 turns the deterministic controller of Gate 48 into an explicit finite-horizon decision process. The generic object records a finite action list, deterministic transition, and reward. `finiteBellmanValue` then computes the usual finite-horizon dynamic-programming value.

For the Gate-48 witness, the immediate reward still favors `exploit`, but the three-step Bellman action value favors `explore`. The exploratory action attains the horizon-three optimum, while exploitation is strictly suboptimal.

Verified core claims:

- `gate49_myopic_q_prefers_exploit`
- `gate49_three_step_q_prefers_explore`
- `gate49_bellman_value_three_start`
- `gate49_explore_attains_bellman_optimum`
- `gate49_exploit_is_bellman_suboptimal`
- `gate49_bellman_derives_rational_exploration`

The result is deterministic dynamic programming, not yet a stochastic MDP. The reward is an explicit declared objective and is not identified with truth or uniquely correct epistemic utility.
