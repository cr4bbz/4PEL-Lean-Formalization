# Modal knowledge classification in 4-PEL

This document collects the currently compiler-verified modal laws of the primitive evidence-stable knowledge operator `K` on the active Lean 4.31 branch.

The purpose is to separate four ingredients that classical modal slogans often blur together:

1. frame geometry such as reflexivity, transitivity, and Euclideanness;
2. four-valued information status `T`, `F`, `B`, `N`;
3. the internal object-language negation `not K phi` versus meta-level absence of positive knowledge;
4. qualitative evidence stability versus probabilistic threshold aggregation.

## 1. Core semantic facts

For an accessible profile of complete FDE values:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N
heterogeneous profile -> K(phi) = F
```

Thus `K` is an evidence-stability operator, not merely a universal positive-support operator.

A second structural fact is forced by the probability axioms themselves:

```text
mu(R_i(w)) = 1
mu([])     = 0
```

imply

```text
R_i(w) != []
```

for every agent and world. Seriality is therefore not an additional frame assumption in the present model class; it is induced by probability normalization.

## 2. Classification table

| Assumptions | Compiler-verified consequence | Boundary / failure |
|---|---|---|
| none beyond the 4-PEL model axioms | every accessibility list is nonempty | induced by `mu_total` and `mu_empty` |
| homogeneous accessible `phi` profile | `K phi` recovers the complete common FDE value | heterogeneity forces strict `F` |
| reflexivity at `w` | `K phi = T -> phi = T` at `w` | this is strict factivity, not unrestricted designated factivity |
| none | `K(phi and psi) = T -> K phi = T` and `K psi = T` | strict conjunction decomposition survives |
| none | `K+ phi` and `K+ psi -> K+(phi and psi)` | positive conjunction elimination fails in general |
| `K+(phi and psi)` | `K+ phi iff Stable(phi)` and analogously right | component stability is the exact extraction boundary |
| local transitivity at `w` | `K+ phi -> value(K K phi) = value(K phi)` | preserves both positive values `T` and `B` exactly |
| local transitivity at `w` | positive axiom 4: `K+ phi -> K+ K phi` | unrestricted positive introspection fails without the frame condition |
| local Euclideanness only | no general positive internal negative introspection | finite countermodel: `not K p` is positive but `K(not K p)` is not |
| local transitivity + local Euclideanness | `value(K K phi) = value(K phi)` for all four values | full-value idempotence |
| local transitivity + local Euclideanness | `value(K(not K phi)) = value(not K phi)` | full-value internal negative introspection |
| local transitivity + local Euclideanness + negative support for `K phi` | `K+(not K phi)` | internal axiom-5 style recovery |
| reflexive + transitive + Euclidean singleton with `K phi = N` | meta-level lack of positive knowledge does not imply `(not K phi)+` | frame geometry cannot eliminate the gap |
| transitive + Euclidean + local NoGap bridge | meta-level lack of positive knowledge implies `K+(not K phi)` | NoGap is an information-status assumption, not a frame condition |
| stable accessible `phi` profile | `K phi = B phi` | both operators recover the same full FDE value |
| arbitrary profile | `K phi = B phi iff Stable(phi) OR B phi = F` | under instability, equality survives only by accidental agreement at `F` |
| positive knowledge | `K+ phi -> B+ phi` | positive belief alone does not imply positive knowledge |
| positive belief | `K+ phi iff Stable(phi)` | stability is the exact upgrade condition |
| `v != F` | `K phi = v iff Stable(phi) AND B phi = v` | all non-false knowledge values require stability |
| arbitrary profile | `K phi = F iff Unstable(phi) OR B phi = F` | `F` is the unique instability-absorbing value |
| arbitrary profile | `K phi = if Stable(phi) then B phi else F` | exact factorization of knowledge through belief plus stability |

Here `K+ phi` abbreviates positive/designated support for `K phi`.

## 3. Axiom 4 phase

Without frame conditions, positive introspection fails: a formula can be stable on the first epistemic horizon and unstable on the second.

Ordinary local transitivity repairs this. The verified result is stronger than the usual positive axiom 4:

```text
K+ phi
+ local transitivity
-> value(K K phi) = value(K phi)
```

Because positive knowledge in FDE can be either `T` or `B`, the theorem gives two fixed points:

```text
K phi = T -> K K phi = T
K phi = B -> K K phi = B
```

The glutty value is not classicalized by introspection.

## 4. Axiom 5 phase

Local Euclideanness alone does not suffice for the present evidence-stable `K`.

The finite countermodel has a root whose successors all see the root successor region, so the root is locally Euclidean. One successor, however, sees an additional world. This changes the complete value of `K p` across the root successors:

```text
K p at root = B
K p at u    = B
K p at v    = F
```

Hence the internal negation varies:

```text
not K p at u = B
not K p at v = T
```

and outer knowledge rejects the heterogeneous profile:

```text
K(not K p) at root = F.
```

Transitivity closes the extra-successor escape route. Together with Euclideanness, source and successor neighborhoods coincide extensionally. The resulting theorem is full-value rather than merely designated:

```text
transitivity + Euclideanness
-> K K phi = K phi
-> K(not K phi) = not K phi.
```

## 5. Meta-level ignorance is a separate axis

The following notions are not identified in 4-PEL:

```text
meta-level: K+ phi = false
object-level: (not K phi)+ = true
negative support: (K phi).neg = true
```

A one-world model with

```text
p = N
R(w) = [w]
```

is reflexive, transitive, and Euclidean, yet:

```text
K p        = N
not K p    = N
K(not K p) = N.
```

Thus even S5-like frame geometry cannot convert lack of positive knowledge into internal negative evidence.

The missing bridge is exactly a NoGap-style semantic condition:

```text
K+ phi = false -> (K phi).neg = true.
```

With this bridge plus transitivity and Euclideanness, positive knowledge of internal ignorance follows.

This yields a two-axis architecture:

```text
frame geometry         -> transport of epistemic values
FDE information status -> interpretation of absence / negation / ignorance
```

## 6. Relation to conjunction and possibility

The same stability mechanism explains two earlier boundaries.

For conjunction:

```text
K+ phi and K+ psi -> K+(phi and psi)
K+(phi and psi) does not imply K+ phi
K+(phi and psi) -> (K+ phi iff Stable(phi)).
```

For possibility, primitive raw accessibility possibility and the internal dual `not K(not phi)` agree exactly when:

```text
Stable(phi) OR Diamond_raw(phi) = T.
```

If the accessible `phi` profile is unstable, internal dualization can force strict `T` even when raw possibility carries a different four-valued profile.

## 7. Knowledge as stability-filtered probabilistic belief

Primitive knowledge `K` and probabilistic threshold belief `B` process the same accessible evidence differently:

```text
K -> requires complete FDE-value stability
B -> thresholds positive and negative probability mass separately.
```

The complete verified theory compresses to one operator equation:

```text
K(phi) = if Stable(phi) then B(phi) else F.
```

This factorization subsumes the earlier equality, upgrade, and four-value classification theorems.

On stable profiles:

```text
K(phi) = B(phi).
```

For positive/designated support:

```text
K+(phi) -> B+(phi)
```

and, assuming positive belief,

```text
K+(phi) iff Stable(phi).
```

At the complete-value level:

```text
K(phi) = T iff Stable(phi) and B(phi) = T
K(phi) = B iff Stable(phi) and B(phi) = B
K(phi) = N iff Stable(phi) and B(phi) = N
K(phi) = F iff Unstable(phi) or B(phi) = F.
```

Thus instability is not low confidence. It is a qualitative failure mode that overrides threshold aggregation and sends knowledge to strict `F`.

## 8. Current necessitation build gate

`PEL4/ModalKnowledgeNecessitationBoundary.lean` is the next local build gate and is not yet counted as compiler-verified.

It tests two distinct possible failures of the classical rule from validity to knowledge-validity.

First, the current `Model` structure does not formally require the explicitly listed `m.worlds` to be closed under accessibility. A candidate strict theorem therefore adds:

```text
w in worlds and w R_i u -> u in worlds
```

and aims to recover:

```text
strict validity + accessibility closure -> strict K-validity.
```

Second, the existing `T/B` knowledge gate is already accessibility-closed while `p` is positively true at every listed world. The candidate counterexample tests whether:

```text
positive validity + accessibility closure
```

can still fail to yield positive `K`-validity because the complete accessible values vary between `T` and `B`.

If the gate builds, necessitation will split into a domain-closure problem for strict validity and an additional stability problem for the positive fragment.

## 9. Current structural picture

The verified modal fragment can now be summarized as follows:

```text
probability normalization -> seriality
reflexivity                -> strict factivity
transitivity               -> positive/full-value-preserving axiom 4 on T/B
Euclideanness alone        -> insufficient for axiom 5
transitivity + Euclidean   -> full K-idempotence and internal negative introspection
NoGap                      -> bridges meta-level ignorance to negative epistemic support
stability                  -> K/B agreement and belief-to-knowledge upgrade
K                          -> exactly stability-filtered B
instability                -> overrides B and forces K = F
```

The notable feature is that familiar epistemic laws split into frame transport, information status, domain coverage, and evidence aggregation. This is a specifically four-valued refinement of the classical correspondence picture.

## 10. Next research questions

The highest-value remaining questions are now:

1. verify the strict-versus-positive necessitation boundary;
2. study dynamic preservation or destruction of epistemic stability under update;
3. determine whether the current local frame conditions admit sharper necessity/minimality theorems;
4. compare the verified 4-PEL correspondence pattern systematically with nonstandard Belnap-Dunn knowledge logics before making novelty claims.
