# Modal knowledge classification in 4-PEL

This document collects the currently compiler-verified modal laws of the primitive evidence-stable knowledge operator `K` on the active Lean 4.31 branch.

The central lesson is that familiar epistemic principles split across four independent structural axes:

1. frame geometry (`R`);
2. four-valued information status (`T`, `F`, `B`, `N`);
3. qualitative full-value stability;
4. probabilistic threshold aggregation and update.

## 1. Core knowledge semantics

For an accessible profile of complete FDE values:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N
heterogeneous profile -> K(phi) = F
```

Thus `K` is an evidence-stability operator, not merely universal positive support.

Probability normalization also forces seriality:

```text
mu(R_i(w)) = 1
mu([])     = 0
```

imply

```text
R_i(w) != []
```

for every agent and world.

## 2. Compiler-verified classification table

| Assumptions | Consequence | Boundary / failure |
|---|---|---|
| model axioms | every accessibility list is nonempty | seriality is induced by probability normalization |
| homogeneous accessible `phi` profile | `K phi` recovers the common complete FDE value | heterogeneity forces strict `F` |
| reflexivity at `w` | `K phi = T -> phi = T` | strict factivity only |
| none | `K(phi and psi) = T -> K phi = T` and `K psi = T` | strict conjunction decomposition survives |
| none | `K+ phi` and `K+ psi -> K+(phi and psi)` | positive elimination fails in general |
| `K+(phi and psi)` | `K+ phi iff Stable(phi)` and analogously right | component stability is exact extraction boundary |
| local transitivity | `K+ phi -> value(K K phi) = value(K phi)` | unrestricted positive introspection fails without it |
| local transitivity + Euclidean | `K K phi = K phi` for all four values | Euclidean alone is insufficient |
| local transitivity + Euclidean | `K(not K phi) = not K phi` | full internal negative introspection |
| transitive + Euclidean + NoGap | lack of positive knowledge implies `K+(not K phi)` | NoGap is information-status, not frame geometry |
| stable profile | `K phi = B phi` | instability may separate them |
| arbitrary profile | `K phi = B phi iff Stable(phi) OR B phi = F` | accidental equality survives only at `F` |
| positive knowledge | `K+ phi -> B+ phi` | positive belief does not imply knowledge |
| positive belief | `K+ phi iff Stable(phi)` | exact belief-to-knowledge upgrade condition |
| `v != F` | `K phi = v iff Stable(phi) AND B phi = v` | every non-false K-value requires stability |
| arbitrary profile | `K phi = F iff Unstable(phi) OR B phi = F` | `F` is the instability absorber |
| arbitrary profile | `K phi = if Stable(phi) then B phi else F` | complete K/B factorization |
| strict validity + accessibility closure | strict validity of `K phi` | hidden accessible worlds otherwise refute necessitation |
| positive validity + accessibility closure | `K phi` positive-valid iff `phi` is stable on every listed accessible range | exact positive necessitation boundary |
| admissible conditionalization + probability-free modal formula | complete FDE value is invariant | `bel` is the only current entry point for `mu`-sensitivity |
| same conditions | accessible stability, outer `K`, and raw possibility are invariant | current update changes only `mu` |
| finite fracture witness | `B p : T/T/T -> T/N/T` | conditionalization can create instability |
| same fracture witness | `K(B p) : T -> F` | instability is amplified by the K gate |
| finite restoration witness | `B p : T/N/T -> T/T/T` | conditionalization can restore stability |
| same restoration witness | `K(B p) : F -> T` | restored stability reopens the belief channel |

Here `K+ phi` abbreviates positive/designated support for `K phi`.

## 3. K/B factorization

The complete verified relation between evidence-stable knowledge and probabilistic threshold belief is:

```text
K(phi) = if Stable(phi) then B(phi) else F.
```

Equivalently:

```text
K(phi) = T iff Stable(phi) and B(phi) = T
K(phi) = B iff Stable(phi) and B(phi) = B
K(phi) = N iff Stable(phi) and B(phi) = N
K(phi) = F iff Unstable(phi) or B(phi) = F.
```

This supports the structural reading:

> knowledge is probabilistic belief passed through a qualitative full-value stability gate.

Instability is therefore not low probability. It is a separate qualitative failure mode that overrides threshold aggregation.

## 4. Introspection and ignorance

Local transitivity repairs positive axiom 4 and preserves complete positive K-values:

```text
K phi = T -> K K phi = T
K phi = B -> K K phi = B
```

For axiom 5, Euclideanness alone is insufficient because a successor may acquire additional evidence worlds. Transitivity closes this extra-successor drift. Together:

```text
transitivity + Euclidean
-> K K phi = K phi
-> K(not K phi) = not K phi.
```

Meta-level ignorance remains independent:

```text
K+ phi = false
```

is not the same as

```text
(not K phi)+ = true.
```

Even reflexive, transitive, Euclidean frames can leave `K phi = N`. A NoGap bridge is required to convert lack of positive knowledge into internal negative epistemic support.

## 5. Necessitation phase

The necessitation phase is complete at the current level of abstraction.

### Strict necessitation

Because model validity quantifies only over the explicit list `m.worlds`, strict necessitation requires accessibility closure:

```text
w in worlds and u in R_i(w) -> u in worlds.
```

Under this condition:

```text
strict-valid(phi) -> strict-valid(K phi).
```

Without it, an unlisted accessible `F` world gives a finite countermodel.

### Positive necessitation

Accessibility closure alone is insufficient because positive validity permits mixtures such as `T/B`.

The exact compiler-verified formula-level boundary is:

```text
positive-valid(phi)
+ accessibility closure
->
(positive-valid(K phi) iff
 phi is full-value stable on every listed accessible range).
```

The corresponding schema-level equivalence is also verified:

```text
positive necessitation
iff
every positively valid formula is accessibility-stable
```

under accessibility closure.

Thus:

```text
strict necessitation   = domain coverage
positive necessitation = domain coverage + full-value stability.
```

## 6. Dynamic conditionalization phase

The old dynamics prototype had an unsafe zero-evidence boundary: raw conditionalization returned `0` at zero evidence mass while model normalization had been postulated unconditionally. This has been repaired.

`conditionalize` now requires an explicit:

```text
ConditionalizationAdmissible m E
```

witness containing positive local evidence mass and normalization obligations. Liar, Surprise Examination, and Surprise Backward Elimination compile through this safe interface.

### 6.1 Probability-free invariance

Current conditionalization changes only `mu` and leaves:

```text
worlds, R, val, c
```

unchanged.

For `ModalProbabilityFree(phi)`, meaning that `phi` contains no `bel` constructor:

```text
value_after(phi) = value_before(phi)
Stable_after(phi) = Stable_before(phi)
K_after(phi) = K_before(phi)
Diamond_after(phi) = Diamond_before(phi).
```

This is compiler-verified for arbitrary nesting of `K`, negation, conjunction, and raw possibility.

### 6.2 Belief-mediated stability fracture

A finite three-world witness gives:

```text
before: B p = T,T,T
after:  B p = T,N,T
```

Hence:

```text
Stable(B p): true -> false
K(B p):       T   -> F.
```

Atomic `p` itself remains invariant under the same update.

### 6.3 Belief-mediated stability restoration

A second finite three-world witness gives the converse phase. Before update:

```text
B p = T,N,T
Stable(B p) = false
K(B p) = F.
```

After admissible conditionalization on `p`:

```text
B p = T,T,T
Stable(B p) = true
K(B p) = T.
```

Thus conditionalization can both create and remove knowledge-relevant instability while leaving `R` and atomic valuation fixed.

The dynamic picture is therefore genuinely bidirectional:

```text
fracture:    stable   -> unstable   -> K(B p): T -> F
restoration: unstable -> stable     -> K(B p): F -> T
```

Working interpretation: **epistemic stability-phase transition**. Conditionalization is neither monotone knowledge gain nor monotone knowledge loss in the current semantics.

## 7. Current structural picture

The verified modal fragment can be compressed to:

```text
probability normalization -> seriality
reflexivity                -> strict factivity
transitivity               -> positive/full-value-preserving axiom 4
transitivity + Euclidean   -> full K-idempotence and internal axiom 5
NoGap                      -> bridges meta-level ignorance to negative support
stability                  -> K/B agreement and belief-to-knowledge upgrade
K                          -> stability-filtered B
instability                -> forces K = F unless B already equals F
accessibility closure      -> restores strict necessitation
closure + stability        -> exact positive necessitation boundary
safe conditionalization   -> requires admissible positive evidence
probability-free fragment  -> dynamically invariant under current update
belief-mediated formulas   -> can cross stability boundaries
stable -> unstable         -> can collapse outer K from T to F
unstable -> stable         -> can restore outer K from F to T
```

The broad research interpretation is increasingly precise: familiar epistemic laws are preservation laws for different structural layers, and failures occur when one layer is transported as though another were invariant.

## 8. Current build gate

`PEL4/ModalDynamicsPhaseClassification.lean` is the next unverified local gate.

It lifts the pointwise K/B factorization to a two-state 2x2 stability table:

```text
stable -> stable     : K tracks B on both sides
stable -> unstable   : posterior K is forced to F
unstable -> stable   : prior K = F; posterior K tracks posterior B
unstable -> unstable : K = F on both sides
```

The gate also packages the fracture and restoration models as witnesses that admissible conditionalization realizes both off-diagonal transitions.

## 9. Next research questions

Highest-value next questions:

1. verify the general dynamic K phase classification;
2. determine exact sufficient conditions for conditionalization to preserve stability even when `bel` occurs;
3. classify which K/B values are dynamically reachable under fixed `R` and valuation;
4. investigate dynamic creation/removal of K-gluts and K-gaps;
5. compare the resulting dynamic correspondence pattern with four-valued dynamic epistemic logics before making novelty claims.
