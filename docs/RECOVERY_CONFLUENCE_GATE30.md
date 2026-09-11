# Gate 30 — Recovery Confluence

## Question

Gate 29 established genuine epistemic path dependence: from one recovered 4PEL model, different admissible evidence futures can stabilize in different Recovery phases.

Gate 30 asks for the complementary positive boundary:

> Under which update conditions does the order of admissible evidence cease to matter for Recovery?

The first clean confluence zone is atomic Conditionalization.

## Static atomic evidence

Conditionalization changes the local probability measure `mu`, but leaves worlds, accessibility, valuation and thresholds unchanged.

For an atomic proposition `p`, its positive evidence event is therefore static across updates:

`{u in R(i,w) | p is positively true at u}`.

This is not true for arbitrary evidence formulas containing belief. A formula such as `B_i phi` can change truth value after an earlier probability update, so its later conditioning event may itself depend on the path.

Gate 30 deliberately proves the atomic theorem first rather than silently assuming this stronger dynamic invariance.

## Two-step Bayes commutation

Let `P` and `Q` be the positive events for two atoms `p` and `q`. Assume:

- the initial model satisfies `ModelProbabilityIntegrity`;
- conditioning on `p` is admissible;
- conditioning on `q` is admissible;
- `q` remains admissible after `p`;
- `p` remains admissible after `q`.

For every duplicate-free local event `S` inside the accessibility support, the `p;q` order reduces to

\[
\frac{\mu(S\cap P\cap Q)/\mu(P)}
     {\mu(P\cap Q)/\mu(P)}
=
\frac{\mu(S\cap P\cap Q)}{\mu(P\cap Q)}.
\]

The reverse order gives

\[
\frac{\mu(S\cap Q\cap P)/\mu(Q)}
     {\mu(Q\cap P)/\mu(Q)}
=
\frac{\mu(S\cap Q\cap P)}{\mu(Q\cap P)}.
\]

Probability integrity makes extensionally equal finite events receive equal mass, and intersection is extensionally commutative. Hence both posterior measures agree on every event that the modal semantics can observe.

This is formalized by:

- `intersectWorlds_comm_extensional`;
- `intersectWorlds_right_swap_extensional`;
- `rat_div_div_same_den_cancel`;
- `conditionalize_two_atoms_measure_eq_on_event`.

## Why observational equivalence instead of raw model equality?

The current `FiniteSet` representation is a `List`. The probability-integrity contract constrains duplicate-free event presentations inside the local accessibility support, but does not require arbitrary duplicate-containing lists to receive extensionally identical raw `mu` values.

Therefore full function equality of the two posterior `mu` fields would state more than the semantic interface currently guarantees.

Gate 30 introduces:

`ModalObservationEquivalent m n`.

It requires equality of:

- worlds;
- accessibility;
- valuation;
- thresholds;
- probabilities on every duplicate-free local event contained in the relevant accessibility range.

This is exactly the information consumed by the modal language.

## Modal semantic invariance

Gate 30 proves that modal observational equivalence preserves the complete FDE value of every modal formula:

\[
m \sim_{\mathrm{obs}} n
\quad\Longrightarrow\quad
\forall \varphi,w,
\operatorname{evalModal}_m(w,\varphi)
=
\operatorname{evalModal}_n(w,\varphi).
\]

The proof is structural over `ModalFormula`:

- atoms use valuation equality;
- negation and conjunction use the induction hypotheses;
- belief uses equality of the threshold-relevant positive and negative event masses;
- knowledge and possibility use equality of accessibility and recursively equal formula values.

The corresponding Lean theorem is:

`evalModal_eq_of_modalObservationEquivalent`.

The same equivalence also preserves `BeliefThresholdComplete`, and therefore recursively preserves compositional Recovery:

`compositionalRecoveryAt_iff_of_modalObservationEquivalent`.

## Main Gate-30 theorem

`conditionalize_two_atoms_observationEquivalent` proves:

\[
C_q(C_p(m)) \sim_{\mathrm{obs}} C_p(C_q(m)).
\]

Consequently, for every modal formula `phi`, the main theorem

`conditionalize_two_atoms_recovery_confluent`

establishes:

\[
\boxed{
\mathrm{Recovery}(C_q(C_p(m)),\varphi)
\leftrightarrow
\mathrm{Recovery}(C_p(C_q(m)),\varphi)
}
\]

whenever both update orders satisfy the stated admissibility and integrity assumptions.

Thus the result is stronger than endpoint agreement for one selected formula: the two posterior paths agree on the semantics of the entire current modal language.

## Relation to Gate 29

Gate 29 and Gate 30 are not contradictory.

Gate 29 compares different evidence futures, for example repeatedly learning `p` versus repeatedly learning `e`. Those paths can settle into different phases.

Gate 30 compares a permutation of the same two static atomic filters:

`p ; q`

versus

`q ; p`.

Under the Gate-30 assumptions, pure ordering cannot create Recovery divergence.

A useful distinction is therefore:

\[
\boxed{
\text{evidence-choice dependence}
\neq
\text{atomic order dependence}
}
\]

The first exists by Gate 29. The second is excluded here under probability integrity and mutual sequential admissibility.

## Interpretation

Atomic Conditionalization forms a commutative subdynamics inside the larger non-monotone 4PEL update system.

A simple picture is two static filters. Passing the epistemic state through filter `P` and then `Q` leaves the same semantically observable posterior as passing through `Q` and then `P`. The intermediate normalizations differ, but Bayes cancellation erases that history at the endpoint.

This gives a concrete confluence boundary inside a framework that otherwise permits genuine epistemic path dependence.

## Boundaries and open extensions

Gate 30 does **not** yet prove:

1. confluence for arbitrary evidence formulas;
2. confluence when an earlier update changes the extension of the later evidence formula;
3. a global Church-Rosser or Newman's-lemma theorem for arbitrary finite update traces;
4. absence of epistemic hysteresis in the full 4PEL dynamics.

Belief-dependent evidence is the natural place where order dependence may re-enter, because the first update can change what counts as the second event.

A later hysteresis gate can therefore ask whether the same informational ingredients, applied in different orders, produce different Recovery endpoints once the evidence itself is dynamically interpreted.
