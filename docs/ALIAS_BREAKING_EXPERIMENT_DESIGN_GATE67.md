# Gate 67 — Alias-Breaking Experiment Design

Gate 66 showed that arbitrarily many repetitions of the existing status sensors cannot resolve the `.fragile` / `.robust` alias. Gate 67 changes the experiment class instead of merely collecting more of the same data.

## Expanded experiment menu

The explicit finite menu contains:

- `statusCheap`: the existing 75/25 coarse Recovery sensor;
- `statusPrecise`: the existing 90/10 coarse Recovery sensor;
- `stressProbe`: a new declared experiment that exposes the robustness distinction.

For `.fragile` and `.robust`, both status sensors remain non-separating. The stress probe instead assigns a Recovery report likelihood of `1/10` to `.fragile` and `9/10` to `.robust`.

## Unique alias breaker

`gate67_unique_alias_breaker` proves, relative to this three-experiment menu,

\[
\operatorname{Separates}(e,\mathrm{fragile},\mathrm{robust})
\iff e=\mathrm{stressProbe}.
\]

Hence `.fragile` / `.robust`, non-identifiable under Gate 64, becomes identifiable after expanding the experiment class.

Starting from the symmetric half-half prior, a Recovery report from the stress probe produces

\[
P(\mathrm{fragile}\mid R)=\frac1{10},\qquad
P(\mathrm{robust}\mid R)=\frac9{10}.
\]

A Non-Recovery report reverses the posterior.

## Structural lesson

Increasing precision about the same coarse observable is not equivalent to measuring a new dimension. If the target distinction lies inside one observational equivalence class, a new intervention can be epistemically more valuable than arbitrarily many repetitions of the old one.

## Boundary

The stress probe is a declared likelihood model. Gate 67 does not derive a physical stress test from 4PEL semantics and does not claim universal experimental identifiability. The theorem is relative to the explicitly specified experiment family.
