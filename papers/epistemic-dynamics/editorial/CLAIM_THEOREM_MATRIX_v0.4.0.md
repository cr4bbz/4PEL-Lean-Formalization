# Claim–Theorem Matrix — Epistemic Dynamics v0.4.0

Purpose: every substantive paper claim must be classifiable as a Lean theorem, an encoded modelling choice, or an interpretation. The matrix records safe wording and the nearest overclaim to avoid.

| ID | Safe paper claim | Class | Lean anchor | Do not claim |
|---|---|---|---|---|
| C95.1 | A failed calibration can reverse an initially suboptimal policy in the explicit degraded-sensor witness. | Lean theorem | `gate95_policy_self_corrects`, `PEL4/SelfCorrectingPolicy.lean` | Calibration universally converges to the correct model. |
| C97.1 | Expanding the finite model class can add an exact-fit hypothesis when both original models exceed the discrepancy tolerance. | Lean theorem | `gate97_open_model_class_witness`, `PEL4/OpenModelClass.lean` | The missing model is automatically discovered. |
| C100.1 | In the encoded surprise controller, the anomaly triggers model-space expansion rather than ordinary closed-class updating. | Lean theorem | `gate100_anomaly_driven_model_expansion`, `PEL4/AnomalyDrivenModelExpansion.lean` | Surprise generically determines the correct new model class. |
| C101.1 | Explicit outside-class mass can preserve normalization while moving adequacy status from `T` to `N`. | Lean theorem | `gate101_unknown_unknowns_bridge`, `PEL4/UnknownUnknowns.lean` | The value `1/2` unknown mass is uniquely Bayesian or universally warranted. |
| C102.1 | Meta-level ignorance `N` and contradictory model evidence `B` are extensionally distinct states in the explicit evidence semantics. | Lean theorem | `gate102_unknownness_is_not_contradiction`, `gate102_meta_contradiction_is_genuine_glut` | Every practical model dispute can be cleanly classified from raw data as `N` or `B`. |
| C103.1 | World status and model status can vary independently in explicit witnesses. | Lean theorem | `gate103_nested_four_valued_epistemics` | Gate 103 alone proves all 16 product states dynamically reachable. |
| C104.1 | The finite controller gives second-order model maintenance priority over world-directed action whenever model status is `N`, `B`, or `F`. | Lean theorem about an encoded policy | `gate104_rational_epistemic_self_trust` | This priority ordering is a universal law of rationality. |
| C105.1 | Under coordinate-local verdict updates, all sixteen canonical nested states are distinct and mutually reachable in at most two updates. | Lean theorem | `gate105_nested_state_reachability`, `PEL4/NestedStateReachability.lean` | Realistic evidence processes make every transition available. |
| C106.1 | In the Gate-92 value witness, calibration beats world sensing exactly below calibration cost `13/200`. | Lean theorem | `gate106_calibration_threshold`, `gate106_cost_sensitive_self_trust` | `13/200` is a general epistemic threshold. |
| C106.2 | The same qualitative `N` model status can support different value-optimal actions at different epistemic costs. | Lean theorem | `gate106_status_alone_does_not_fix_action` | Four-valued status by itself always determines rational action. |
| C107.1 | Two quantitative beliefs can compress to the same `T/T` nested status while selecting different utility-optimal actions. | Lean theorem | `gate107_four_valued_projection_not_control_sufficient`, `gate107_four_valued_sufficiency_challenge` | 4PEL is representationally inadequate or refuted. |
| C108.1 | For the encoded gap and contradiction repairs, the local tension `posSupport * negSupport` strictly decreases and the result is classical. | Lean theorem | `gate108_epistemic_repair_dynamics` | The product is a universal entropy or epistemic-quality measure. |
| C109.1 | Under the successful-repair oracle, every nested state reaches the classical `T/F x T/F` region within at most two repair steps. | Lean theorem conditional on model definition | `gate109_two_steps_reach_stable`, `gate109_self_correction_liveness` | Every real agent can acquire the evidence needed for such a repair. |
| C110.1 | If target-different worlds are observationally aliased, no observation-only policy can be uniformly correct on both. | Lean theorem | `gate110_observational_aliasing_limit` | Self-correction is impossible in every richer observation channel. |
| C110.2 | Termination/classicalization need not imply truth under aliasing. | Lean theorem in witness | Gate-109 connection inside `PEL4/ObservationalAliasingLimit.lean` | A stable 4PEL state is necessarily false or unreliable. |
| C111.1 | A supplied disambiguating experiment restores truth-guaranteeing decoding and a stable truth-aligned repaired state in the Gate-110 witness. | Lean theorem | `gate111_active_identification_restores_truth_guaranteeing_repair` | Every observational alias admits a separating intervention. |
| C112.1 | In the symmetric finite witness, perfect identification is worth buying over blind commitment exactly when cost is below `1/2`. | Lean theorem | `gate112_cost_of_identifiability` | The value of identifiability is universally `1/2`. |
| C113.1 | Once safe unresolvedness is an action, there are coherent finite value models in which preserving `N` is value-optimal. | Lean theorem | `gate113_rational_unresolvedness`, `PEL4/RationalUnresolvedness.lean` | Ignorance is generally preferable to inquiry or action. |
| C113.2 | In this witness, identification beats unresolvedness exactly below cost `2/5`. | Lean theorem | `gate113_identification_vs_unresolved_threshold` | `2/5` is a universal inquiry threshold. |
| C114.1 | A truth-guaranteeing decoder exists iff the target is constant on every observation fiber. | Lean theorem | `gate114_truth_guaranteeing_decoder_iff_fiber_consistent`, `PEL4/GeneralIdentifiability.lean` | The theorem supplies an efficient decoder-learning algorithm. |
| C114.2 | Full hidden-world identification is stronger than necessary for a target-specific task. | Formal consequence / interpretation | Gate-114 criterion | Hidden-world distinctions are never epistemically relevant. |
| C114.3 | The decoder-existence direction is noncomputable and uses classical choice for generic fibers. | Formal implementation fact | `gate114Decoder` | The construction is computationally extracted from Lean as an efficient policy. |
| C115.1 | The explicit pair of experiments is target-separating although neither singleton nor the empty family is. | Lean theorem | `gate115_minimal_target_experiment_family`, `PEL4/MinimalTargetExperimentFamily.lean` | The pair is globally minimum-cost over arbitrary experiments. |
| C115.2 | Target identification may succeed while full world identification fails, when the remaining aliases share the same target. | Lean theorem | `gate115_pair_not_world_identifying`, `gate115_remaining_alias_is_target_harmless` | All unresolved hidden-state differences are harmless. |
| C116.1 | With a known symmetric `4/5` sensor, one sample yields posterior `4/5` or `1/5` and remains `N` under the explicit `9/10` control bridge. | Lean theorem + modelling threshold | `gate116_one_positive_posterior`, `gate116_one_signal_remains_unresolved` | Posterior `4/5` logically implies `N` independently of the chosen bridge. |
| C116.2 | Two agreeing samples yield posterior `16/17` or `1/17`, causing `T/F` commitment under the encoded threshold policy. | Lean theorem + modelling threshold | `gate116_double_positive_posterior`, `gate116_double_negative_posterior`, `gate116_two_signal_statuses` | Two agreeing samples establish logical certainty. |
| C116.3 | Even after `++`, the negative world retains likelihood `1/25 > 0`. | Lean theorem | `gate116_double_positive_does_not_logically_eliminate_negative` | Control commitment eliminates the alternative world. |
| C116.4 | Under noise, confidence sufficient for an encoded control decision can coexist with non-elimination of the alternative. | Formal synthesis / interpretation | `gate116_noisy_identification` | Posterior confidence and logical truth are the same semantic object. |

## Modelling choices that must be marked as such

- Gate 104 priority ordering.
- Gate 105 direct coordinate-update transition relation.
- Gate 106 / 112 / 113 utility and cost models.
- Gate 108 tension function `posSupport * negSupport`.
- Gate 109 successful-repair oracle.
- Gate 111 availability of a perfectly separating intervention.
- Gate 113 safe-deferral value `3/5`.
- Gate 116 prior `1/2`, sensor reliability `4/5`, conditional independence, and the posterior-to-4PEL control threshold `9/10`.

## Paper-wide wording rule

Use **verified** only for Lean theorems or exact computations. Use **encoded**, **assumed**, **chosen**, or **witness-specific** for modelling decisions. Use **suggests**, **supports an interpretation**, or **can be read as** for philosophical conclusions. Never let a successful `native_decide` theorem turn a finite model design choice into a universal normative statement.