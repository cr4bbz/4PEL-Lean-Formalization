# Gate 5 — Classical recovery from evidential regularity

## Research question

Can classical logic be recovered as a structurally stable fragment of 4-PEL once the underlying evidence geometry is sufficiently complete, consistent, and independently supported, rather than by globally postulating bivalence?

This gate treats LEM and EFQ as target phenomena to be explained, not as principles that must be either globally assumed or globally rejected.

## Core decomposition

For a realized four-valued evidence state:

- **channel completeness** means at least one of the positive/negative evidence channels is supported;
- **channel consistency** means the two channels are not jointly supported;
- **channel regularity** is completeness plus consistency;
- **modal stability** is separate from local regularity and propagates a recovered classical value through an accessibility range;
- **nonloop regularity** strengthens occupancy by requiring residual independent channel capacity.

At the value level:

- gap-free excludes `N`;
- glut-free excludes `B`;
- gap-free + glut-free isolates exactly `{T,F}`.

## Verified Gate 5 results

### G5.1 — Geometry/value correspondence

For `RealizesFDE polarity A v`:

1. `GapFreeValue v ↔ ChannelComplete polarity A`;
2. `GlutFreeValue v ↔ ChannelConsistent polarity A`;
3. `ChannelRegular polarity A ↔ IsClassicalValue v`.

This is the basic recovery bridge:

`complete + consistent evidence ↔ {T,F}`.

The classical slice is therefore recovered inside the four-valued semantics rather than obtained by deleting `N` and `B` by fiat.

### G5.2 — Classical propositional subalgebra

The recovered `{T,F}` slice is closed under the existing FDE operations:

- negation;
- conjunction;
- disjunction.

This establishes a value-level classical propositional fragment of the existing algebra.

### G5.3 — LEM and EFQ have different recovery conditions

The formal split is:

- tolerant/designated `p ∨ ¬p` iff the value is gap-free;
- strict-`T` excluded middle iff the value lies in `{T,F}`;
- LP ex falso from `p ∧ ¬p` is restored under glut-freedom.

The LP ex-falso result is deliberately read as a semantic recovery under an undesignated contradiction premise. It is not a global proof-theoretic completeness result.

Hence LEM and EFQ do not return for the same structural reason.

### G5.4 — Stability means persistence, not local bivalence

Local channel regularity already yields `T/F`.

`StableAt` is needed for a different result: if the current value is regular and stable, every accessible world carries the same recovered classical value.

Thus:

`local classical recovery != modal persistence of classical recovery`.

### G5.5 — Deletion robustness and fragility

Gate 4 minors give two complementary results:

- deleting one member of a same-polarity parallel pair preserves channel completeness, consistency, and regularity;
- deleting the unique representative of a polarity from regular evidence destroys completeness and forces every realized residual FDE value to `N`.

So a classical state can be both genuine and structurally fragile.

### G5.6 — Structural classicality through nonloop capacity

Define:

- `NonloopChannelComplete`;
- `NonloopChannelConsistent`;
- `NonloopChannelRegular`.

These use `supportsNonloopChannel` rather than ordinary ground occupancy.

Before minors, the canonical finite channel matroid is loopless, so:

`NonloopChannelRegular ↔ ChannelRegular`.

After contraction this can fail sharply. If `c` is contracted from channel-regular evidence:

- the contracted polarity has no remaining nonloop support;
- regularity already excludes the opposite polarity;
- therefore the minor is not nonloop-complete and not nonloop-regular.

If a parallel same-polarity atom remains, ordinary ground support can still be present while nonloop support is absent.

This formalizes the distinction:

`classical-valued occupancy != classicality sustained by residual independent information`.

## Current interpretation

The original hypothesis now separates into three layers:

1. **coverage** removes evidential gaps;
2. **consistency** removes evidential gluts;
3. **informational stability** concerns persistence and residual independent capacity under transformations.

The first two recover a local classical value. The third asks whether that recovery is structurally robust rather than merely visible in the coarse `T/F` projection.

## Success criteria

Gate 5 counts as successful when:

- the local recovery theorems compile;
- LEM and EFQ recovery conditions are formally separated;
- modal stability is proved to propagate, rather than create, local classicality;
- deletion robustness and deletion fragility are both witnessed;
- occupancy regularity is compared with nonloop regularity before and after contraction;
- selected declarations pass the strict axiom audit;
- manuscript v0.9 records the verified results and scope boundaries.

## Nonclaims

Gate 5 does **not** claim:

- that classical logic is globally correct;
- that every real evidence system is matroidal;
- that FDE/4-PEL should be replaced by classical logic;
- that modal stability is necessary for local bivalence;
- that structural matroid contraction is identical with belief revision or epistemic acceptance;
- completeness of a classical proof system for the recovered fragment;
- that value-level LP ex falso already proves unrestricted formula-level EFQ on arbitrary 4-PEL models.

## Next research boundary

Two natural continuations remain:

1. **formula-level recovery**: assume regular atomic valuations, prove by induction that the propositional language remains in `{T,F}`, and then study which modal operators preserve that fragment;
2. **fine-grained recovery**: lift the recovery predicates to the reliability refinement and test whether independent-capacity classicality survives coarse projection and minors.
