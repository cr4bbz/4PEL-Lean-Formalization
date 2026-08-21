# Modal knowledge classification in 4-PEL

This document collects the currently compiler-verified modal laws of the primitive evidence-stable knowledge operator `K` on the active Lean 4.31 branch.

The purpose is to separate three ingredients that classical modal slogans often blur together:

1. frame geometry such as reflexivity, transitivity, and Euclideanness;
2. four-valued information status `T`, `F`, `B`, `N`;
3. the internal object-language negation `not K phi` versus meta-level absence of positive knowledge.

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
K p       = N
not K p   = N
K(not K p)= N.
```

Thus even S5-like frame geometry cannot convert lack of positive knowledge into internal negative evidence.

The missing bridge is exactly a NoGap-style semantic condition:

```text
K+ phi = false -> (K phi).neg = true.
```

With this bridge plus transitivity and Euclideanness, positive knowledge of internal ignorance follows.

This yields a two-axis architecture:

```text
frame geometry        -> transport of epistemic values
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

## 7. Current structural picture

The verified modal fragment can be summarized as follows:

```text
probability normalization -> seriality
reflexivity               -> strict factivity
transitivity              -> positive/full-value-preserving axiom 4 on T/B
Euclideanness alone       -> insufficient for axiom 5
transitivity + Euclidean  -> full K-idempotence and internal negative introspection
NoGap                     -> bridges meta-level ignorance to negative epistemic support
```

The notable feature is that familiar modal laws split into a frame-transport component and an information-status component. This is a specifically four-valued refinement of the classical correspondence picture.

## 8. Next research questions

The modal-law program is no longer at the basic axiom-4/axiom-5 discovery stage. The highest-value remaining questions are now:

1. characterize necessitation-like principles for positive versus strict truth;
2. classify `K`/probabilistic-`B` interaction, including when knowledge entails threshold belief;
3. study dynamic preservation or destruction of epistemic stability under update;
4. determine whether the current local frame conditions admit sharper necessity/minimality theorems;
5. compare the verified 4-PEL correspondence pattern systematically with nonstandard Belnap-Dunn knowledge logics before making novelty claims.
