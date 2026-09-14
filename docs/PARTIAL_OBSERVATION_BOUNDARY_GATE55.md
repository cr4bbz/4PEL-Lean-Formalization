# Gate 55 — Partial Observation Boundary

## Question

Can the visible Recovery/Non-Recovery signal be treated as the complete Markov state of the controlled epistemic process?

## Observation map

Gate 55 deliberately exposes only one coarse bit:

- `recovery`: `start`, `fragile`, `robust`;
- `nonRecovery`: `destabilized`, `integrating`, `broken`.

The hidden state remains the full Gate-47 epistemic state.

## Aliasing witness

`fragile` and `robust` generate exactly the same visible observation. Nevertheless they differ in every quantity that becomes important after Gate 54:

- calibration error: 1 versus 0;
- external truth alignment: false versus true;
- stress robustness: false versus true.

Thus the Recovery bit does not determine calibration, truth alignment, or robust Recovery.

## Transition boundary

The failure is dynamic as well as static. Under the same action `explore`:

- `fragile → destabilized`, whose observation is `nonRecovery`;
- `robust → robust`, whose observation remains `recovery`.

Hence equal current observations plus the same action do not determine the same next observation. The Recovery observation therefore fails deterministic observation-level Markov sufficiency.

## Main conclusion

For this observation regime,

\[
o(s)=o(t)
\not\Rightarrow
\text{same calibration, truth status, robustness, or observed transition}.
\]

A controller restricted to the Recovery bit cannot legitimately identify that bit with its full decision state. A hidden-state or belief-state treatment is formally motivated, which is the entry point to the finite epistemic POMDP in Gate 56.

## Boundary

This is not a theorem that every compressed observation map fails or that POMDPs are uniquely mandatory. It is a verified insufficiency result for the concrete Recovery-bit observation map over the existing Gate-47/48 dynamics.
