# Gate 68: Adaptive Experiment Design and Stopping

Gate 67 established a structural boundary: the existing status sensors cannot distinguish `.fragile` from `.robust`, while an added stress probe can. Gate 68 turns that result into a posterior-dependent controller.

## Question

Can the agent derive which experiment to run from its current Bayesian belief and stop once the hidden-state distinction is sufficiently resolved?

## Identification objective

For the fragile/robust pair, define confidence as the larger posterior mass:

\[
C(b)=\max\{b(\text{fragile}),b(\text{robust})\}.
\]

For an experiment `e`, Gate 68 evaluates the one-step expected posterior confidence

\[
EC(e,b)=\sum_o P(o\mid e,b)\,C(b^{e,o}).
\]

The finite experiment selector chooses an experiment maximizing this declared objective over the Gate-67 menu.

## Verified witness

At the symmetric aliased prior,

\[
C(b_0)=\frac12.
\]

Both old status experiments remain trapped at

\[
EC(\text{statusCheap},b_0)=EC(\text{statusPrecise},b_0)=\frac12.
\]

The stress probe reaches

\[
EC(\text{stressProbe},b_0)=\frac9{10},
\]

and strictly dominates both old experiments. Therefore the finite argmax selects `stressProbe`.

With the declared stopping threshold

\[
\tau=\frac9{10},
\]

the unresolved prior samples the stress probe. Either possible stress outcome produces posterior confidence exactly \(9/10\), so the policy stops immediately afterward. A further precise status report instead leaves the alias unresolved and the policy still chooses the stress probe.

## Main theorem

`gate68_adaptive_experiment_design_and_stopping`

The theorem packages the complete witness:

1. initial confidence is `1/2`;
2. both old experiments have expected confidence `1/2`;
3. the stress probe has expected confidence `9/10`;
4. the selector chooses the stress probe;
5. the unresolved policy samples it;
6. either stress observation triggers stopping;
7. old status evidence does not trigger stopping.

## Interpretation

The result sharpens Gate 66 and Gate 67. Repetition is useful only when the experiment exposes the hidden distinction. Once the experiment family contains an alias-breaking intervention, the current posterior can itself determine that the new intervention is preferable.

The resulting loop is

\[
b_t\to\operatorname*{argmax}_e EC(e,b_t)\to o_t\to b_{t+1}\to \text{stop/sample}.
\]

This is the first explicit adaptive Bayesian experiment-selection rule in the current 4PEL control chain.

## Boundary

The confidence functional, threshold, likelihoods, and experiment menu are declared parts of a finite witness. Gate 68 does not establish that maximum posterior mass is the uniquely correct uncertainty measure, nor that the myopic selector is globally optimal over arbitrary horizons. The stress probe is still an explicit experiment-model extension rather than something derived from physical 4PEL semantics.

The next natural step is sequential Bayesian experiment design with sensing cost, where stopping itself becomes an optimization result: sample only when the expected value of another experiment exceeds its acquisition cost.
