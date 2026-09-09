# Gate 5 — Classical recovery from evidential regularity

## Research question

Can classical logic be recovered as a structurally stable fragment of 4-PEL once the underlying evidence geometry is sufficiently complete and consistent, rather than by globally postulating bivalence?

This gate treats LEM and EFQ as target phenomena to be explained.

## Core decomposition

For a realized four-valued evidence state:

- **channel completeness** means at least one of the positive/negative evidence channels is supported;
- **channel consistency** means the two channels are not jointly supported;
- **channel regularity** is completeness plus consistency;
- **stability** is kept separate from local regularity and is used to propagate a recovered classical value through a modal accessibility range.

At the value level:

- gap-free excludes `N`;
- glut-free excludes `B`;
- gap-free + glut-free isolates exactly `{T,F}`.

## Gate 5 theorem targets

### G5.1 — Geometry/value correspondence

Prove, for `RealizesFDE polarity A v`:

1. `GapFreeValue v ↔ ChannelComplete polarity A`;
2. `GlutFreeValue v ↔ ChannelConsistent polarity A`;
3. `ChannelRegular polarity A ↔ IsClassicalValue v`.

This is the main recovery bridge from evidence geometry to the classical value slice.

### G5.2 — Classical subalgebra

Show that the recovered `{T,F}` slice is closed under the existing FDE operations:

- negation;
- conjunction;
- disjunction.

The point is not merely that `T` and `F` exist in FDE, but that the regular slice is internally stable under the propositional operations already used by 4-PEL.

### G5.3 — Separate recovery of LEM and EFQ

Formalize the asymmetry:

- tolerant/designated `p ∨ ¬p` is recovered from gap-freedom alone;
- strict-`T` excluded middle characterizes the full classical slice;
- LP ex falso from `p ∧ ¬p` is recovered from glut-freedom alone.

Hence LEM and EFQ do not return for the same structural reason.

### G5.4 — Stability as persistence, not local classicality

Prove that local regularity already gives `T/F`; modal stability then propagates that recovered classical value through every accessible world.

This distinguishes:

`local classical recovery != modal persistence of classical recovery`.

### G5.5 — Minor stability

Connect Gate 5 to the Gate 4 minor layer.

Primary questions:

1. Does deletion of a parallel representative preserve `ChannelRegular`?
2. Can deletion of a unique representative destroy completeness and move a classical state into `N`?
3. Can contraction preserve ground occupancy while destroying independent channel capacity, and what notion of classical recovery should be invariant under that operation?

The intended distinction is between **value classicality** and **structural robustness of classicality under evidence change**.

## Success criteria

Gate 5 is complete when:

- the local recovery theorems compile;
- LEM and EFQ recovery conditions are formally separated;
- the role of modal stability is proved rather than merely described;
- at least one nontrivial minor-preservation or minor-failure theorem is proved;
- selected declarations pass the strict axiom audit;
- manuscript v0.9 records the theorem statements, scope boundaries, and failed/remaining conjectures.

## Nonclaims

Gate 5 does **not** claim:

- that classical logic is globally correct;
- that every real evidence system is matroidal;
- that FDE/4-PEL should be replaced by classical logic;
- that modal stability is necessary for local bivalence;
- that structural matroid contraction is identical with belief revision or epistemic acceptance;
- completeness of a proof system for the recovered fragment.

The target is narrower and stronger: identify exact structural conditions under which classical behavior is recovered inside the existing four-valued semantics.
