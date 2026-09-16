# Epistemic Dynamics v0.4.0 — Lean Source Audit, Gates 95–116

Status: editorial contract for the Gate-116 paper refresh.

## Provenance rule

Every numerical, structural, or theorem-level claim in the paper must be checked against the Lean source in the branch where that gate was verified. The newest cumulative research branch does not physically retain every older specialist module, so absence from the Gate-116 tree must never be treated as evidence that an older result disappeared. Historical results are sourced from their dedicated green gate branches; Gates 105–116 are also inherited by the Gate-116 research line.

Paper prose must distinguish three classes:

1. **Lean theorem** — exactly mechanized and safe to state as verified.
2. **Model assumption / definition** — encoded by construction, not discovered by proof.
3. **Interpretation** — philosophical or methodological reading of the formal result; never presented as a Lean theorem.

## Mandatory corrections to v0.3.0

The old Gate-104 manuscript contains several factual mismatches. They must not survive into v0.4.0.

### Gate 95

Source: `PEL4/SelfCorrectingPolicy.lean`, branch `research/self-correcting-policy-gate95`.

Correct values:

- overconfident prior: reliable `4/5`, degraded `1/5`;
- failed-calibration evidence: `6/25`;
- posterior after failure: reliable `1/3`, degraded `2/3`;
- initial action: fragile;
- corrected action: safe;
- objective values under the true degraded model: fragile `1/10`, safe `3/5`.

The v0.3.0 values `9/10`, `9/17`, `8/17` are incorrect for the verified Gate-95 source.

### Gate 97

Source: `PEL4/OpenModelClass.lean`, branch `research/open-model-class-gate97`.

Correct witness:

- old low model predicts `1/10`;
- old high model predicts `9/10`;
- omitted balanced model predicts `1/2`;
- observed positive rate is `1/2`;
- both old squared discrepancies are `4/25`;
- tolerance is `1/10`;
- the balanced unknown model has discrepancy `0`.

The paper must use squared discrepancy, not substitute an unrelated absolute-error witness.

### Gates 99–100

Sources: `PEL4/PosteriorSurprise.lean` and `PEL4/AnomalyDrivenModelExpansion.lean` on their dedicated branches.

Verified structural chain:

- anomaly predictive evidence is `3/200`;
- surprise threshold is `1/20`;
- anomaly triggers `modelDoubt`;
- Gate 100 maps this to `expandUnknown`;
- routine evidence leaves the known class closed.

Gate 100 decides **when to expand**, not how to synthesize the missing model.

### Gate 101

Source: `PEL4/UnknownUnknowns.lean`, branch `research/unknown-unknowns-gate101`.

Correct open belief:

- closed: `(low, high, unknown) = (1/2, 1/2, 0)`;
- doubt: `(1/4, 1/4, 1/2)`;
- known mass supports adequacy, unknown mass supports inadequacy;
- the anomaly-induced adequacy status is `N`;
- total probability remains normalized.

The v0.3.0 two-mass description `(known, unknown) = (3/4,1/4)` is not the verified Gate-101 witness.

### Gate 102

Source: `PEL4/ContradictoryModelEvidence.lean`, branch `research/contradictory-model-evidence-gate102`.

Correct explicit evidence states:

- gap: `(1/2,1/2) -> N`;
- conflict: `(4/5,4/5) -> B`;
- validated: `(9/10,1/10) -> T`;
- refuted: `(1/10,9/10) -> F`.

The theorem-level point is that second-order unknownness `N` and contradiction `B` are formally distinct.

### Gate 103

Source: `PEL4/NestedFourValuedEpistemics.lean`, branch `research/nested-four-valued-epistemics-gate103`.

Verified result: world status and model status form separate `FDEValue` coordinates. Explicit witnesses show the same world status with model `T/N/B`, and the same trusted-model status with world `T/F/B/N`.

Boundary: Gate 103 gives witness-level coordinate independence; it does **not** prove that all sixteen pairs are reachable under one dynamics. Gate 105 later supplies that result for an intentionally permissive coordinate-update system.

### Gate 104

Source: `PEL4/RationalEpistemicSelfTrust.lean`, branch `research/rational-epistemic-self-trust-gate104`.

The action type has **five** actions:

- `actPositive`
- `actNegative`
- `senseWorld`
- `calibrateModel`
- `reconcileModel`

Verified priority:

- model `N` -> `calibrateModel`;
- model `B` -> `reconcileModel`;
- model `F` -> `calibrateModel`;
- only model `T` licenses direct interpretation of the world coordinate;
- trusted-model world `N/B` -> `senseWorld`;
- trusted-model world `T` -> `actPositive`;
- trusted-model world `F` -> `actNegative`.

The old manuscript's `actFragile/actSafe/expandModelClass` presentation is not Gate 104 and must be replaced.

Boundary: this is a finite deterministic priority policy, not a universal norm of rational agency.

## Gates 105–116: verified extension

### Gate 105 — Nested State Reachability

Source: `PEL4/NestedStateReachability.lean`, branch `research/nested-state-reachability-gate105`.

Verified: the sixteen canonical `(world, model)` four-valued states are pairwise distinct and, under the explicit coordinate-local update relation, every state reaches every other state in at most two updates.

Boundary: updates directly install diagnostic verdicts. This proves structural reachability, not realistic evidence dynamics.

### Gate 106 — Cost-Sensitive Self-Trust

Source: `PEL4/CostSensitiveSelfTrust.lean`, branch `research/cost-sensitive-self-trust-gate106`.

Verified in the Gate-92 value witness:

- calibration beats world sensing iff `cost < 13/200`;
- calibration beats acting now iff `cost < 17/200`;
- the same qualitative model status `N` can induce different optimal actions at different costs.

Boundary: thresholds are witness-specific.

### Gate 107 — Four-Valued Sufficiency Challenge

Source: `PEL4/FourValuedSufficiencyChallenge.lean`, branch `research/four-valued-sufficiency-challenge-gate107`.

Two normalized quantitative beliefs project to the same nested `T/T` status but induce different utility-optimal actions: `99/100` positive mass chooses risky, whereas `3/4` chooses safe against a safe value of `4/5`.

Verified conclusion: the chosen qualitative four-valued projection is **not universally control-sufficient**.

Do not write: “4PEL is insufficient.” The theorem targets decision sufficiency of this compression, not qualitative representational usefulness.

### Gate 108 — Epistemic Repair Dynamics

Source: `PEL4/EpistemicRepairDynamics.lean`, branch `research/epistemic-repair-dynamics-gate108`.

Local potential: `tension = posSupport * negSupport`.

Verified concrete decreases:

- gap repair: `6/25 -> 9/100`;
- contradiction repair: `16/25 -> 9/100`;
- the concrete repairs end in classical `T/F` states.

Boundary: this is a Lyapunov-like witness for the encoded repairs, not a universal epistemic entropy.

### Gate 109 — Self-Correction Liveness

Source: `PEL4/SelfCorrectionLiveness.lean`, branch `research/self-correction-liveness-gate109`.

Verified under the explicit successful-repair oracle:

- defect count is at most two;
- every unstable step strictly decreases defect count;
- stable states are fixed points;
- every nested state reaches a classical `T/F x T/F` region within at most two repair steps;
- model defects are repaired before world defects.

Boundary: the repair oracle is intentionally strong. Liveness is conditional on successful repair being informationally available.

### Gate 110 — Observational Aliasing Limit

Source: `PEL4/ObservationalAliasingLimit.lean`, branch `research/observational-aliasing-limit-gate110`.

Verified: two hidden worlds can generate the same observation while requiring different target verdicts. Therefore no policy using only that aliased observation can be uniformly correct. Gate-109-style classicalization may terminate while still selecting the wrong truth value.

Conclusion: `liveness != truth` under observational aliasing.

Boundary: impossibility is relative to the specified observation channel.

### Gate 111 — Active Identification Repair

Source: `PEL4/ActiveIdentificationRepair.lean`, branch `research/active-identification-repair-gate111`.

Verified: a supplied `disambiguate` experiment produces different signals for the Gate-110 worlds; the decoder then reconstructs the correct target and the resulting nested state is classically stable and truth-aligned.

Boundary: existence of the separating experiment is an assumption of the witness. The gate does not prove that every alias is breakable.

### Gate 112 — Cost of Identifiability

Source: `PEL4/CostOfIdentifiability.lean`, branch `research/cost-of-identifiability-gate112`.

Verified finite value model:

- blind classical commitment has expected value `1/2`;
- perfect diagnostic gross value is `1`;
- net diagnostic value is `1-cost`;
- diagnostic is strictly preferred iff `cost < 1/2`;
- ties fall to blind commitment by definition.

Boundary: the `1/2` threshold is not universal.

### Gate 113 — Rational Unresolvedness

Source: `PEL4/RationalUnresolvedness.lean`, branch `research/rational-unresolvedness-gate113`.

Verified finite value model:

- safe unresolvedness has value `3/5`;
- blind commitment has value `1/2`;
- perfect identification beats unresolvedness iff `cost < 2/5`;
- at the high-cost witness `1/2`, the controller chooses `remainUnresolved`;
- the preserved visible state has world `N` under trusted model `T`.

Boundary: `3/5` is an explicit utility assignment, not a universal value of ignorance.

### Gate 114 — General Identifiability Criterion

Source: `PEL4/GeneralIdentifiability.lean`, branch `research/general-identifiability-gate114`.

General theorem:

`exists truth-guaranteeing decoder` iff `target is constant on every observation fiber`.

This subsumes Gate 110 as failure of fiber consistency and Gate 111 as a positive instance.

Boundary: the reverse direction constructs a decoder using classical choice and a default off-image verdict. It is an existence theorem, not an efficient synthesis algorithm.

### Gate 115 — Minimal Target-Separating Experiment Family

Source: `PEL4/MinimalTargetExperimentFamily.lean`, branch `research/minimal-target-experiment-family-gate115`.

Verified finite witness:

- neither single experiment nor the empty family is target-separating;
- the pair `[first, second]` is target-separating;
- the pair is nevertheless not world-identifying because worlds `a` and `b` remain aliased;
- that remaining alias is harmless for the target because both require `T`.

Boundary: minimality is only inclusion-minimal inside the explicit two-experiment menu, not a general minimum-cost set theorem.

### Gate 116 — Noisy Identification

Source: `PEL4/NoisyIdentification.lean`, branch `research/noisy-identification-gate116`, green HEAD `875ed5d3850271927fdffe983ca4eca48af9cfed`.

Verified noisy witness:

- symmetric prior `1/2`;
- sensor correctness `4/5`, misleading probability `1/5`;
- no one-signal deterministic decoder is truth-guaranteeing on channel support;
- one positive signal gives posterior `4/5`, one negative `1/5`, both mapped to `N` under the explicit `9/10` control threshold;
- two agreeing positives give `16/17 -> T`;
- two agreeing negatives give `1/17 -> F`;
- conflicting signals return to posterior `1/2 -> N`;
- after `++`, the negative world still has likelihood `1/25 > 0`.

Verified conceptual separation: confidence can be sufficient for the encoded control policy without logically eliminating the alternative world.

Boundary: the `9/10` bridge is a control convention; the sensor is known, symmetric, and conditionally independent. Measurement cost, reliability learning, correlated noise, and optimal stopping are not yet included.

## Paper architecture implied by the audit

The Gate-116 paper should no longer be organized as a chronological pile of gates. The verified results support the following argumentative structure:

1. Foundations and recovery.
2. Control, filtering, and active experimentation.
3. Model uncertainty and calibration.
4. Model criticism and nested self-trust, ending at Gate 104.
5. Self-correction and repair dynamics, Gates 105–109.
6. Identifiability, active repair, and rational unresolvedness, Gates 110–115.
7. Noisy epistemic control, Gate 116.
8. Interpretation and limits.

This audit is normative for paper wording: if manuscript prose conflicts with the Lean source or a boundary above, the prose must change.