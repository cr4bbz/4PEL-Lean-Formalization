# Gate 66 — Repeated Evidence and Posterior Learning

Gate 66 separates two fundamentally different reasons for epistemic uncertainty.

## Identifiable uncertainty

For the identifiable hidden-state pair `.robust` / `.destabilized`, repeated Recovery reports from the precise Gate-64 sensor progressively concentrate posterior mass on `.robust`:

\[
\frac12 \to \frac9{10} \to \frac{81}{82} \to \frac{729}{730}.
\]

The verified theorem `gate66_identifiable_repetition_strictly_concentrates` proves strict improvement across these first three repeated measurements.

## Structural aliasing

For the symmetric prior on `.fragile` / `.robust`, Gate 65 already established that every available Gate-64 sensor assigns the two states the same likelihood for every observation. Gate 66 strengthens this into an exact repeated-learning boundary:

`gate66_alias_survives_all_repetitions`

proves that for every Gate-64 sensor, every fixed observation and every finite repetition count `n`, the posterior remains exactly the original half-half prior.

Thus more samples can reduce statistical uncertainty only when the experiment already exposes a relevant difference. Repetition cannot manufacture an identifying dimension absent from the likelihood model.

## Boundary

The increasing numerical sequence is a finite exact witness, not a general asymptotic Bayesian consistency theorem. The no-learning result is exact within the declared Gate-64 experiment family and the symmetric `.fragile` / `.robust` prior.
