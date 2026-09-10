# Gate 12: directional threshold-wall recovery

## Research question

Which directed crossings of positive and negative support create or remove gaps
and gluts, and under which integrity assumptions do they exactly characterize
preservation of compositional recovery?

Gate 12 is implemented in `PEL4/DirectionalThresholdRecovery.lean`. It refines
the symmetric threshold-straddling and wall-count results into an oriented
account of support gain and loss.

## Directed one-dimensional motion

For threshold `c` and ordered endpoints `before`, `after`, the development
distinguishes four exhaustive motions:

```text
stays below : before < c and after < c
rises       : before < c and c <= after
falls       : c <= before and after < c
stays above : c <= before and c <= after.
```

The previous symmetric `ThresholdStraddles` relation is exactly the disjunction
of `ThresholdRises` and `ThresholdFalls`. Rise and fall have the Boolean
signatures `false -> true` and `true -> false` respectively.

## Exact phase classification

The two threshold coordinates generate the FDE square:

```text
N=(0,0)  T=(1,0)  F=(0,1)  B=(1,1).
```

For a prior classical state, posterior gap creation has exactly two forms:

```text
T -> N : positive falls and negative stays below
F -> N : negative falls and positive stays below.
```

Posterior glut creation likewise has exactly two forms:

```text
T -> B : positive stays above and negative rises
F -> B : negative stays above and positive rises.
```

A prior gap becomes threshold-complete exactly when at least one coordinate
rises. This separates restoration from mere undirected displacement.

## Recursive recovery theorem

`ModalFormula.NoDirectionalGapAt` follows the syntax and accessibility
recursion of the Gate-10 and Gate-11 recovery contracts. At each reachable
belief node it excludes the exact directed gap pattern.

On a probability-integrity prior model, if `phi` is recovered before an
admissible conditionalization, Lean proves:

```text
CompositionalRecovery updated phi
iff
NoDirectionalGap before E hAdm phi.
```

This replaces the abstract posterior-completeness obligation from Gate 11 by a
numerical and oriented explanation: recovery fails precisely where the last
active support side falls while the other side remains below threshold.

## Gap versus glut boundary

The recursive Gate-10 recovery certificate explicitly requires threshold
completeness. It therefore detects gap creation. Excluding posterior gluts also
requires threshold consistency, supplied in the classical-evaluation theorem
by `ModelProbabilityIntegrity`.

Within Gate 12, the minimal `ConditionalizationAdmissible` interface supplies
only positive conditioning mass and the two basic normalization fields; the
module does not itself derive full posterior probability integrity. Gate 13
subsequently closes this boundary: prior `ModelProbabilityIntegrity` plus the
existing admissibility proof is sufficient to derive posterior integrity. Glut
exclusion still additionally needs a classical accessible subformula profile.

## Finite witnesses

Three existing model families instantiate the directional theory:

- the instability witness realizes a directed gap pattern at world `b`;
- the restoration witness leaves `N` by an upward threshold crossing;
- the complete reachability family realizes `T -> B` by a negative rise while
  positive support stays above.

These are theorem-level instantiations, not merely numerical illustrations.

## Theorem map

| Declaration | Role |
| --- | --- |
| `ThresholdRises/Falls/StaysBelow/StaysAbove` | oriented one-coordinate motion |
| `thresholdStraddles_iff_rises_or_falls` | directed decomposition of straddling |
| `thresholdMotion_exhaustive` | four-way motion classification |
| `thresholdPair_T_to_N_iff` | exact positive-fall gap transition |
| `thresholdPair_F_to_N_iff` | exact negative-fall gap transition |
| `thresholdPair_N_to_nonGap_iff` | exact rise-based restoration |
| `thresholdPair_T_to_B_iff` | exact negative-rise glut transition |
| `thresholdPair_F_to_B_iff` | exact positive-rise glut transition |
| `classical_thresholdPair_to_N_iff_directionalGap` | unified classical-to-gap result |
| `classical_thresholdPair_to_B_iff_directionalGlut` | unified classical-to-glut result |
| `beliefThresholdComplete_iff_evalModal_bel_ne_N` | completeness/gap bridge |
| `conditionalization_*_iff_directional*` | modal belief specializations |
| `postUpdateBeliefCompleteAt_iff_noDirectionalGapAt` | recursive local bridge |
| `compositionalRecovery_conditionalize_iff_noDirectionalGap` | Gate-12 main theorem |

## Audit and reproduction

```powershell
lake build
lake env lean PEL4/DirectionalThresholdRecoveryAxiomAudit.lean
```

The focused audit contains twenty Gate-12 declarations. They depend only on
Lean's standard logical principles (`propext`, `Classical.choice`, and
`Quot.sound`) and introduce no project-specific or native axiom.

## Current nonclaims

Gate 12 does not establish:

- preservation of `ModelProbabilityIntegrity` by conditionalization (this is
  subsequently established in Gate 13);
- a continuous or measure-theoretic intermediate-value theorem;
- unrestricted exclusion of posterior gluts;
- recovery preservation for product updates or arbitrary model changes;
- a proof calculus for directed recovery transitions.

## Recommended next gate

Gate 13 answers this question without adding a strengthened update axiom:
integrity of the prior and existing positive-mass admissibility already derive
integrity of the posterior. See
`docs/CONDITIONALIZATION_PROBABILITY_INTEGRITY_GATE13.md`.
