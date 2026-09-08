# Gate 4 - Genuine matroid minors for coarse 4-PEL evidence

## Research question

What changes when Gate 1-3 evidence closure is promoted from an ambient-type closure operator to a matroid closure with an explicit finite ground set, so that deletion and contraction are genuine minors?

## Formal layer

`PEL4/MatroidEvidenceMinors.lean` introduces:

- `GroundMatroidClosure`
- `FiniteGroundMatroidClosure`
- `GroundMatroidClosure.delete`
- `GroundMatroidClosure.contract`
- `GroundMatroidClosure.IsLoop`
- `finiteChannelMatroid`

The minor formulas are

```text
E(M \ D)       = E(M) \ D
cl_(M \ D)(A)  = cl_M(A) \ D

E(M / C)       = E(M) \ C
cl_(M / C)(A)  = cl_M(A ∪ C) \ C
```

Both constructions are Lean-proved to preserve the explicit-ground closure matroid axioms, including exchange.

## Channel consequences

### Deletion

If `x` and `y` are distinct atoms of the same polarity and `y` remains in the ground set, deleting `x` preserves both coarse support bits and therefore the realized FDE value.

If `c` is the unique representative of its polarity, deleting `c` removes exactly that support channel and leaves the opposite channel unchanged.

This separates two notions:

```text
closure redundancy != unconditional removability
```

A member of a circuit is removable while a parallel representative remains. The last representative of a channel is not redundant for the coarse FDE observation.

### Contraction

For the finite channel matroid:

```text
e is a loop in M / c
iff
  e is in the original ground,
  e != c,
  polarity(e) = polarity(c).
```

Thus contraction turns every remaining parallel partner into a loop and no opposite-polarity atom into a loop.

`PEL4/MatroidEvidenceMinorSemantics.lean` therefore defines `supportsNonloopChannel` and proves:

- the original finite channel matroid is loopless;
- before minors, ordinary channel support equals nonloop support;
- after contracting `c`, the channel of `c` has no nonloop support;
- every other channel has nonloop support after contraction iff it had ordinary support before contraction.

## Main conceptual result

Gate 1 identified channel rank with the number of present positive/negative support bits. Gate 4 exposes the scope of that identification.

Before minors the canonical channel matroid is loopless, so polarity occupancy and independent channel capacity coincide. After contraction, an atom can remain in the ground set while becoming a loop. Therefore:

```text
polarity occupancy != residual independent-information capacity
```

Support presence and rank must be tracked separately in minor models.

## Epistemic boundary

The three operations below must not be conflated:

```text
source deletion
!= structural matroid contraction
!= remembered background acceptance
```

Deletion removes evidence from the problem. Matroid contraction quotients by a structural direction and removes the contracted atom from the residual ground set. An epistemic update that remembers accepted evidence needs an additional memory/background component.

Gate 4 therefore does not identify matroid contraction with AGM contraction, Bayesian conditioning, public announcement, or evidence acceptance.

## Trust inventory

The generic deletion/contraction constructors, loop characterization, finite channel matroid, unique-channel deletion profile, and nonloop-capacity theorems are axiom-free in Lean 4.31.

The existing packaged `realizesFDE_delete_parallel_iff` proof currently uses only the repository's allowed standard Lean axioms through a generic equality case split. No project-specific axiom or native evaluation is introduced.

## Falsification criteria

Gate 4 fails if any of the following occurs:

1. deletion or contraction does not satisfy the explicit-ground closure matroid axioms;
2. contraction creates a loop outside the contracted atom's polarity class in the canonical channel matroid;
3. deleting one member of a parallel pair changes a coarse support bit while another same-polarity representative remains;
4. the paper identifies structural contraction with a memory-bearing epistemic update without an additional formal state component.

## Gate 5 candidate

Lift the minor layer to the six-cell reliability refinement. Ask whether a fine-grained matroid can be constructed so that deletion and contraction commute with coarse projection to the two-channel minors. This tests whether reliability merely refines parallel classes or breaks the coarse matroid-minor correspondence.
