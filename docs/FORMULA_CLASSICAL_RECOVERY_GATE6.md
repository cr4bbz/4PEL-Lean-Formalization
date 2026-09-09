# Gate 6 — Formula-level classical recovery

## Research question

Can the value-level classical sector isolated in Gate 5 be lifted compositionally to formulas, and which 4-PEL operators preserve or destroy that recovered classicality?

The target is no longer merely

`regular evidence -> T/F value`,

but

`regular atomic valuation -> classical formula semantics`,

with explicit operator-by-operator boundaries.

## G6.1 — Propositional structural induction

Define the belief-free fragment of the legacy `Formula` syntax and prove:

`AtomicClassicalAt m w -> IsPropositional phi -> IsClassicalValue (eval m w phi)`.

The proof must use the Gate-5 closure theorems for FDE negation and conjunction rather than a new truth table.

Corollaries:

- the syntactic OR macro preserves the fragment;
- material implication preserves the fragment;
- formula-level excluded middle is strictly `T`;
- formula-level contradiction is strictly `F`;
- LP explosion is recovered relative to regular propositional valuations.

## G6.2 — Belief as a recovery boundary

Atomic classicality alone must not be silently extended across Lockean belief.

Construct a finite witness with only `T/F` atomic values but a balanced accessible profile at threshold `3/5`, so that

`B_i p = N`.

This proves:

`atomic classicality != full Formula classicality`.

The conceptual reason is probabilistic indecision, not contradiction: both support events can fall below the Lockean threshold.

## G6.3 — Exact belief recovery condition

Next target: characterize the additional local condition needed for belief to preserve the classical sector.

Candidate decomposition:

1. **non-glut condition**: positive and negative belief thresholds cannot both be met;
2. **decisiveness condition**: at least one threshold is met;
3. together: the belief output is exactly `T` or `F`.

The strong finite-probability integrity layer should be used where complement/additivity claims are required. The weak legacy `Model` interface must not be treated as a genuine probability measure without the extra certificate.

## G6.4 — Modal operator preservation

Lift the analysis to `ModalFormula`.

Questions:

- Does raw possibility preserve `{T,F}` when every accessible input value is classical?
- Does evidence-stable knowledge preserve `{T,F}` under the same hypothesis?
- What happens on empty accessibility ranges?
- Which conditions are necessary for nested `bel`, `know`, and `poss` formulas?

Expected structural asymmetry:

- Boolean/FDE propositional operations preserve classicality compositionally;
- `poss` should preserve classicality on classical accessible profiles;
- `know` should preserve classicality on classical accessible profiles, with instability collapsing to `F`;
- `bel` requires an additional probabilistic decisiveness condition.

These are theorem targets, not assumptions.

## G6.5 — Relation to the existing CPEL translation

The repository already contains `tr_pos` and `tr_neg` into `CPELFormula`, but its completeness-reduction claim is currently documentation rather than a Lean theorem.

Gate 6 must not cite that comment as established completeness.

After the direct formula-recovery layer is verified, compare it to the translation and determine what can actually be proved about collapse of the positive/negative translations on regular valuations.

## Success criteria

Gate 6 is complete when:

- propositional formula recovery is proved by structural induction;
- strict formula-level LEM and restricted formula-level EFQ are derived;
- a classical-atoms / nonclassical-belief counterexample is verified;
- an exact sufficient condition for belief preservation is formalized;
- `know` and `poss` preservation boundaries are proved or counterexampled;
- selected declarations pass the strict axiom audit;
- manuscript v0.10 records both the positive recovery theorem and the operator boundaries.

## Nonclaims

Gate 6 does not yet claim:

- unrestricted classicality of every 4-PEL formula;
- unrestricted classical completeness of the 4-PEL proof system;
- that atomic bivalence alone makes Lockean belief bivalent;
- that the legacy probability interface provides finite additivity;
- that the existing CPEL translation comment constitutes a mechanized completeness theorem.
