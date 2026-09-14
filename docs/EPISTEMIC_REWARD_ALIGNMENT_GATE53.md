# Gate 53 — Epistemic Reward Alignment

Gate 53 introduces a two-parameter reward family over the Gate-48 controller: `recoveryWeight` rewards ordinary recovered states and `robustBonus` gives an additional reward to the verified robust Recovery state.

For the three-step witness, immediate exploration yields `recoveryWeight + robustBonus`, while pure exploitation yields three ordinary Recovery rewards. Therefore the sufficient threshold

`recoveryWeight + recoveryWeight < robustBonus`

forces the exploratory schedule to dominate. Conversely, below or at that threshold exploitation is not worse.

Verified core claims:

- `gate53_immediate_explore_return_formula`
- `gate53_always_exploit_return_formula`
- `gate53_alignment_threshold_selects_exploration`
- `gate53_below_threshold_exploitation_not_worse`
- `gate53_naive_recovery_reward_prefers_exploitation`
- `gate53_aligned_reward_prefers_exploration`
- `gate53_reward_design_controls_epistemic_policy`

The theorem aligns reward with the finite robustness objective only. It does not identify robust Recovery with truth or with general AI alignment.
