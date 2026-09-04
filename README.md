# 4-PEL: Four-Valued Probabilistic Epistemic Logic

4-PEL is a **Lean 4 formalized framework for studying epistemic paradoxes** through the interaction of probabilistic evidence, four-valued semantics, threshold belief, evidence-stable knowledge, modal possibility, aggregation, self-reference, conflict structure, and information update.

The project began as the formal backbone for *The Cartography of Paradoxes: Unifying Probabilistic Epistemic Logic and Non-Bivalent Validity*. The active research branch now goes substantially beyond that original scope, especially through the Preface conflict-geometry program, a four-valued modal knowledge/knowability layer, and a broader investigation of **paradoxes as failures of structural transport**.

> [!IMPORTANT]
> **Research status:** This repository contains machine-checked theorems, executable finite models, and explicitly marked research directions. Claims described as **Lean-verified** have compiled successfully on the active research branch with Lean 4.31. Interpretive names and broader philosophical theses remain working research terminology unless stated otherwise.

> [!NOTE]
> The paper PDF in the repository is a snapshot of an earlier stage. The active branch contains substantial results not yet incorporated into that manuscript.

---

## Core idea

4-PEL combines Lockean threshold reasoning with Belnap-Dunn / First Degree Entailment (FDE). A proposition can occupy one of four states:

| State | Positive support | Negative support | Reading |
| --- | ---: | ---: | --- |
| `T` | yes | no | supported as true |
| `F` | no | yes | supported as false |
| `B` | yes | yes | glut / overdetermination |
| `N` | no | no | gap / underdetermination |

For probabilistic belief `B_i`, positive and negative support are thresholded independently:

```text
B_i(phi).pos iff P_pos(phi) >= c_i
B_i(phi).neg iff P_neg(phi) >= c_i.
```

The modal layer contains an evidence-stable primitive knowledge operator `K_i` and primitive raw accessibility possibility `Diamond_i`. These are deliberately distinct from probabilistic belief and from the internal abbreviation `not K_i(not phi)`.

---

## Verified research results

### 1. Glut boundary

If positive and negative belief both cross the threshold, a minimum amount of glut mass is unavoidable:

```text
P_B >= 2c - 1.
```

In the scaled integer formalization:

```text
P_B >= 2c - 100.
```

### 2. Lottery and Preface non-agglomeration

Threshold belief is not generally closed under conjunction. For the symmetric Preface construction, the characteristic threshold boundary is:

```text
1/2 < c <= n/(n+1).
```

### 3. Preface conflict geometry

For exact conflict masses `x_A` and shared co-conflict masses `J_A`:

```text
J_Q = sum_{A superset Q} x_A.
```

Generic Möbius reconstruction recovers exact incidence from the full hierarchy. The fixed-marginal affine fiber has generic freedom:

```text
2^n - n - 2
```

for `n >= 2`.

Positive co-conflict support forms downward-closed simplicial complexes. In the three-claim fixed-marginal fiber, Lean verifies profiles with identical coarse data but different support-nerve signatures and Euler counts. General homology and persistence remain open.

### 4. Knowledge Stability Principle

The evidence-stable four-valued knowledge operator recovers homogeneous accessible status exactly:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N.
```

Heterogeneous complete FDE status forces `K(phi) = F`.

Internal negation of knowledge is not generally identical to meta-level absence of positive knowledge.

### 5. Knowledge conjunction boundary

Positive knowledge is closed under conjunction introduction:

```text
K+(phi) and K+(psi) -> K+(phi and psi).
```

Unrestricted positive conjunction elimination fails. Under `K+(phi and psi)`, the exact boundary is:

```text
K+(phi) iff Stable(phi)
K+(psi) iff Stable(psi).
```

At the strict layer, however:

```text
K(phi and psi) = T -> K(phi) = T and K(psi) = T.
```

### 6. Raw possibility versus the internal knowledge dual

Primitive raw possibility is not globally equivalent to `not K(not phi)`. Lean verifies:

```text
Diamond_raw(phi) = not K(not phi)
iff
Stable(phi) OR Diamond_raw(phi) = T.
```

Under instability, the internal dual can collapse to strict `T`, erasing four-valued information carried by raw possibility.

### 7. Modal frame classification of `K`

The main factivity and introspection boundaries are now Lean-verified:

```text
probability normalization -> every accessibility list is nonempty
reflexivity               -> strict factivity
transitivity              -> K+ phi implies value(K K phi) = value(K phi)
Euclideanness alone       -> insufficient for positive internal axiom 5
transitivity + Euclidean  -> K K phi = K phi for all four values
transitivity + Euclidean  -> K(not K phi) = not K phi
NoGap                     -> bridges meta-level ignorance to negative support
```

Thus the glutty positive value `B` is preserved by positive introspection rather than classicalized. A separate reflexive-transitive-Euclidean singleton witness with `K phi = N` shows that even S5-like frame geometry cannot turn meta-level lack of positive knowledge into internal negative evidence.

See `docs/MODAL_KNOWLEDGE_CLASSIFICATION.md` for the full table and countermodel map.

### 8. Church-Fitch phase classification

The modal satisfaction/validity layer, raw knowability principle, local/global Fitch recovery, no-gap independence, strict-truth phase, raw-vs-dual separation, and final Church-Fitch classification are Lean-verified.

A representative positive raw collapse has the form:

```text
positive raw knowability
+ global source NoGap
+ uniform Fitch recovery
+ global source NoGlut
-> positive omniscience
   + strict-truth positive omniscience
   + strict knowledge omniscience.
```

Raw possibility and internal dual possibility are not interchangeable. The repository contains a finite witness where dualized knowability is positive although witness-bearing raw knowability is not.

### 9. Fitch: object-language fracture and recovery

For the Moorean formula

```text
M(p) = p and not K(p)
```

a finite model verifies:

```text
K(M(p))       = B
K(p)          = F
K(not K(p))   = F.
```

Thus positive conjunction extraction fails in exactly the Fitch-shaped case. Recovery is obtained under the local package:

```text
reflexivity
+ Stable(phi)
+ no-glut for K(phi).
```

The repository also contains finite independence witnesses and global raw-knowability transport theorems.

### 10. Knower fixed-point bifurcation

Lean verifies:

```text
T -> F
F -> T
B -> B
N -> N.
```

The nonclassical values are fixed points while the classical values form a two-cycle.

### 11. Sorites threshold geometry

For exclusive signed evidence on a 0--100 scale and `c > 50`, the gappy region is exactly:

```text
100 - c < x < c
```

with width `2c - 100`. The same slack occurs as the minimum glut-overlap lower bound.

### 12. Surprise Examination: dynamic reversal and context transport

Successive truthful updates verify:

```text
belief(exam Friday):      F -> N -> T
belief(not exam Friday):  T -> N -> F.
```

The backward-elimination extension verifies that each day is predictable in its special elimination context while none is positively predicted initially. Working diagnosis: **context-indexed prediction transport failure**.

### 13. Finite Fine-Grainedness and population-prospect geometry

The population-axiology research branch isolates Finite Fine-Grainedness as
finite-path connectivity of a slight-difference graph. Lean verifies that
reflexivity, transitivity, and local transport propagate comparisons along such
paths, while a two-tier lexical carrier supplies a disconnected countermodel.

The first 4-PEL bridge is also explicit: finite-chain support plus independent
rejection yields the glut value `B` rather than arbitrary derivability. Two
affine support paths with the same classical endpoints `T -> F` have different
midpoint phases (`N` versus `B`), showing that convex interpolation restores a
path without forcing bivalence.

Gate 2 adds normalized finite population prospects, a rational four-cell
evidence kernel `Population -> Delta^3`, and a quantifier-faithful contract for
Risky General Non-Extreme Priority. An exact-length chain theorem isolates the
`r` applications of a reciprocal risk increment `p` with `r * p = 1`. If those
steps support an endpoint comparison while an independent condition rejects
it, Lean derives the 4-PEL value `B`; a finite witness keeps an unrelated claim
at `N`. A focused axiom audit is compiled in CI. See
`docs/FINITE_FINE_GRAINEDNESS_4PEL.md` for hypotheses and formalization limits.

---

## Paradox map

| Paradox / family | Structural pressure point | Current 4-PEL diagnosis | Status |
| --- | --- | --- | --- |
| Lottery | thresholding vs conjunction | non-commutation | Lean-verified model |
| Preface | local acceptance vs global interaction | projection loss / fiber underdetermination | Lean-verified research program |
| Moore | truth vs belief status | level separation | executable model |
| Liar | self-reference + contradiction | glut-compatible behavior without explosion | executable model + ex-falso theorem |
| Knower | epistemic self-reference | nonclassical fixed-point bifurcation | Lean-verified |
| Sorites | gradual evidence vs categorical status | threshold gap/glut geometry | Lean-verified |
| Surprise Examination | update and backward elimination | dynamic reversal + context transport failure | Lean-verified |
| Fitch / Church-Fitch | knowability, Moorean conjunction, possibility duality | stability reflection + transport + NoGap/NoGlut phase boundaries | Lean-verified conditional classification |
| Population axiology | finite small-step chains + reciprocal-risk interpolation | connectivity transport; normalized evidence-kernel lift to non-trivial `B` | Lean-verified Gate 2 structural core |

---

## Paradoxes as failures of structural transport

A recurring pattern is that paradoxical reasoning assumes that some epistemically important property survives a transformation.

Schematically:

```text
rich structure E  --T-->  transformed structure E'
     |                         |
     pi                        pi
     v                         v
coarse state S  --T*-->   coarse state S'
```

A paradoxical inference may behave as if:

```text
pi(T(E)) = T*(pi(E))
```

must hold. The repository now exhibits projection loss, non-commutation, nonclassical fixed points, threshold phase changes, dynamic status reversal, context-indexed transport failure, higher-order interaction loss, stability-reflection failure, and modal-duality collapse under epistemic instability.

The strongest case studies follow a three-stage pattern:

```text
identify a hidden transport principle
-> build a countermodel
-> characterize hypotheses that recover the transport.
```

---

## Architecture

Core and epistemic modules include:

```text
PEL4/FDE.lean
PEL4/Model.lean
PEL4/Belief.lean
PEL4/EpistemicStatus.lean
PEL4/KnowledgeSemantics.lean
PEL4/KnowledgeSanity.lean
PEL4/KnowledgeConjunctionBoundary.lean
PEL4/KnowledgeConjunctionIntroduction.lean
PEL4/KnowledgePossibilityBoundary.lean
PEL4/ModalLanguage.lean
PEL4/ModalValidity.lean
PEL4/ModalKnowledgeLaws.lean
PEL4/ModalKnowledgeStrictLaws.lean
PEL4/ModalKnowledgeTransitive.lean
PEL4/ModalKnowledgeNegativeIntrospection.lean
PEL4/ModalKnowledgeIgnoranceBoundary.lean
PEL4/Dynamics.lean
```

Church-Fitch modules include:

```text
PEL4/Paradoxes/Fitch.lean
PEL4/Paradoxes/FitchRecovery.lean
PEL4/Paradoxes/FitchRecoveryIndependence.lean
PEL4/Paradoxes/FitchKnowabilityBoundary.lean
PEL4/Paradoxes/ChurchFitch.lean
PEL4/Paradoxes/ChurchFitchNoGapIndependence.lean
PEL4/Paradoxes/ChurchFitchPhaseLandscape.lean
PEL4/Paradoxes/ChurchFitchClassification.lean
```

Research notes:

```text
docs/MODAL_KNOWLEDGE_CLASSIFICATION.md
docs/PARADOX_TRANSPORT_RESEARCH.md
docs/RESEARCH_QUESTIONS.md
docs/CONFLICT_NERVE_RESEARCH.md
```

---

## Build and verification

The project intentionally avoids a Mathlib dependency. For the active branch:

```bash
git clone https://github.com/cr4bbz/4PEL-Lean-Formalization.git
cd 4PEL-Lean-Formalization
git checkout research/preface-case-study
lake build
```

A successful `lake build` checks every module imported by `PEL4.lean`.

---

## Research boundaries

Several distinctions remain explicit:

- `B_i(phi)` is probabilistic threshold belief, not knowledge.
- Internal FDE negation is not generally meta-level absence of support.
- Primitive raw `Diamond` is not definitionally the same as `not K not`.
- The Liar and Gödel-inspired modules are not complete formalizations of semantic diagonalization or incompleteness.
- Conflict-Nerve Euler/signature results are formalized; general homology and persistence are not.
- Dynamic evidence-stable knowledge remains largely open.
- The zero-evidence conditionalization boundary in the dynamics layer still needs repair before strong general dynamic claims.
- Exact necessity/minimality of every modal frame correspondence is not yet proved.
- Novelty claims for the combined structural and modal terminology require a systematic literature audit.

The project aims to distinguish **theorem, finite model, interpretation, and novelty claim** rather than collapse them into one layer.

---

## Current research direction

The detailed agenda is maintained in `docs/RESEARCH_QUESTIONS.md`. The modal axiom-4/axiom-5 discovery phase is now consolidated. Near-term priorities are:

1. classify interaction between evidence-stable `K` and probabilistic `B`;
2. prove sharper necessity/minimality results for modal frame correspondences;
3. repair the zero-evidence conditionalization boundary;
4. study dynamic preservation and destruction of `K` under update;
5. prove global independence/minimality results for Church-Fitch packages;
6. expand the structural-transport abstraction across paradox families;
7. deepen Conflict-Nerve topology to homology and persistence;
8. perform a systematic literature/novelty audit before publication claims.

4-PEL is best read as a machine-checkable laboratory for the geometry, dynamics, modal structure, and information loss behind epistemic paradoxes.
