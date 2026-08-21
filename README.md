# 4-PEL: Four-Valued Probabilistic Epistemic Logic

4-PEL is a **Lean 4 formalized framework for studying epistemic paradoxes** through the interaction of probabilistic evidence, four-valued semantics, threshold belief, knowledge, modal possibility, aggregation, self-reference, conflict structure, and information update.

The project began as the formal backbone for *The Cartography of Paradoxes: Unifying Probabilistic Epistemic Logic and Non-Bivalent Validity*. The active research branch now goes substantially beyond that original scope, especially through the Preface conflict-geometry program, a four-valued knowledge/knowability layer, and a broader investigation of **paradoxes as failures of structural transport**.

> [!IMPORTANT]
> **Research status:** This repository contains a mixture of machine-checked theorems, executable finite models, and explicitly marked research directions. Claims described below as **Lean-verified** have been successfully compiled on the active research branch with Lean 4.31. Interpretive names and broader philosophical theses remain working research terminology unless stated otherwise.

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

The newer modal layer also contains an evidence-stable knowledge operator `K_i` and primitive raw accessibility possibility `Diamond_i`. These are deliberately kept distinct from probabilistic belief and from the internal abbreviation `not K_i(not phi)`.

---

## Verified research results

### 1. Glut Boundary

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

Generic Möbius reconstruction recovers exact incidence from the full hierarchy. At full resolution:

```text
exact incidence x_A
<-> co-conflict hierarchy J_A
<-> weighted conflict filtration f(A).
```

The fixed-marginal affine fiber has generic freedom:

```text
2^n - n - 2
```

for `n >= 2`.

### 4. Conflict Nerve

Positive co-conflict support forms downward-closed simplicial complexes. In the three-claim fixed-marginal fiber, Lean verifies profiles with identical coarse data but different support-nerve signatures and Euler counts, including:

```text
edge + isolated vertex     chi = 2
triangle boundary          chi = 0
filled triangle            chi = 1.
```

This is the finite combinatorial core of the working **topological conflict underdetermination** result. General homology and persistence remain open.

### 5. Knowledge Stability Principle

The evidence-stable four-valued knowledge candidate recovers homogeneous accessible status exactly:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N.
```

Heterogeneous complete FDE status forces `K(phi) = F`.

Internal negation of knowledge is not generally identical to absence of positive knowledge. Lean verifies that the two coincide exactly when the knowledge value is classical.

### 6. Knowledge conjunction boundary

Positive knowledge is closed under conjunction introduction:

```text
K+(phi) and K+(psi) -> K+(phi and psi).
```

Unrestricted positive conjunction elimination fails. Under the premise `K+(phi and psi)`, the exact boundary is:

```text
K+(phi) iff Stable(phi)
K+(psi) iff Stable(psi).
```

Working diagnosis: **stability reflection boundary**.

### 7. Raw possibility versus the internal knowledge dual

Primitive raw possibility is not globally equivalent to:

```text
not K(not phi).
```

Lean verifies the exact boundary:

```text
Diamond_raw(phi) = not K(not phi)
iff
Stable(phi) OR Diamond_raw(phi) = T.
```

Under instability, the internal dual collapses to strict `T`, which can erase glut/gap information carried by raw possibility.

### 8. Conservative modal object language

`PEL4/ModalLanguage.lean` adds primitive `K` and primitive raw `Diamond` without mutating the legacy `Formula` syntax. Every old formula embeds conservatively:

```text
evalModal(embed(phi)) = eval(phi).
```

### 9. Fitch: object-language fracture and local recovery

`PEL4/Paradoxes/Fitch.lean` encodes the actual Moorean formula:

```text
M(p) = p and not K(p).
```

A Lean-verified finite model has a reflexive critical witness where:

```text
K(M(p))       = B
K(p)          = F
K(not K(p))   = F.
```

Thus:

```text
K+(p and not K p) -/-> K+(p)
```

in exactly the Fitch-shaped case. The compound is stable while its components are unstable.

`PEL4/Paradoxes/FitchRecovery.lean` proves the converse local boundary: positive knowledge of `phi and not K(phi)` is inconsistent with the combined assumptions

```text
reflexivity
+ Stable(phi)
+ no-glut for K(phi).
```

The concrete Fitch countermodel satisfies reflexivity and no-glut but violates `Stable(p)`, isolating component instability as its escape route.

`PEL4/Paradoxes/FitchKnowabilityBoundary.lean` is the current build gate. It lifts the local result through primitive raw possibility and must not be marked verified until a successful build is reported.

### 10. Knower fixed-point bifurcation

Lean verifies:

```text
T -> F
F -> T
B -> B
N -> N.
```

Thus the nonclassical values are fixed points while the classical values form a two-cycle.

### 11. Sorites threshold geometry

For exclusive signed evidence on a 0--100 scale and `c > 50`, the gappy region is exactly:

```text
100 - c < x < c
```

with width `2c - 100`. The same slack occurs as the minimum glut-overlap lower bound when positive and negative support both reach threshold.

### 12. Surprise Examination: dynamic reversal and context transport

Successive truthful updates verify:

```text
belief(exam Friday):      F -> N -> T
belief(not exam Friday):  T -> N -> F.
```

The backward-elimination extension verifies that each day is predictable in its special elimination context while none is positively predicted initially. Working diagnosis: **context-indexed prediction transport failure**.

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
| Fitch | knowability, knowledge and Moorean conjunction | stability-reflection failure + duality boundary | local fracture/recovery Lean-verified; global gate active |

---

## Paradoxes as failures of structural transport

The earlier heuristic, **paradoxes as projection errors**, explains Lottery and Preface but is too narrow. A broader pattern is that paradoxical reasoning often assumes that some epistemically important property survives a transformation.

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

must hold. The repository now exhibits:

- projection loss,
- non-commutation,
- nonclassical fixed points,
- threshold phase changes,
- dynamic status reversal,
- context-indexed transport failure,
- higher-order interaction loss,
- stability-reflection failure,
- modal-duality collapse under epistemic instability.

The strongest case studies increasingly follow a three-stage pattern:

```text
identify a hidden transport principle
-> build a countermodel
-> characterize hypotheses that recover the transport.
```

Fitch is currently the clearest example of this pattern.

---

## Architecture

Core and epistemic modules include:

```text
PEL4/FDE.lean
PEL4/Model.lean
PEL4/Belief.lean
PEL4/Syntax.lean
PEL4/EpistemicStatus.lean
PEL4/StructuralTransport.lean
PEL4/KnowledgeSemantics.lean
PEL4/KnowledgeSanity.lean
PEL4/KnowledgeConjunctionBoundary.lean
PEL4/KnowledgeConjunctionIntroduction.lean
PEL4/KnowledgePossibility.lean
PEL4/KnowledgePossibilityBoundary.lean
PEL4/ModalLanguage.lean
PEL4/Dynamics.lean
```

Paradox and research modules include:

```text
PEL4/Paradoxes/Lottery.lean
PEL4/Paradoxes/Preface*.lean
PEL4/Paradoxes/Moore.lean
PEL4/Paradoxes/Liar.lean
PEL4/Paradoxes/Knower.lean
PEL4/Paradoxes/Sorites.lean
PEL4/Paradoxes/SurpriseExamination.lean
PEL4/Paradoxes/SurpriseBackwardElimination.lean
PEL4/Paradoxes/Fitch.lean
PEL4/Paradoxes/FitchRecovery.lean
PEL4/Paradoxes/FitchKnowabilityBoundary.lean
```

Research notes:

```text
docs/PARADOX_TRANSPORT_RESEARCH.md
docs/RESEARCH_QUESTIONS.md
docs/CONFLICT_NERVE_RESEARCH.md
```

---

## Build and verification

The project intentionally avoids a Mathlib dependency. Finite models use exact rational probabilities where convenient, while several generic inequalities use scaled integer encodings.

For the active branch:

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
- Surprise currently studies dynamic threshold belief; dynamic evidence-stable knowledge remains open.
- The local Fitch fracture and recovery results are verified, but a full Church-Fitch theorem schema still requires a modal satisfaction/validity layer and an explicit formula-quantified knowability principle.
- Novelty claims for the combined structural terminology require a systematic literature audit.

The project aims to distinguish **theorem, finite model, interpretation, and novelty claim** rather than collapse them into one layer.

---

## Current research direction

The detailed agenda is maintained in `docs/RESEARCH_QUESTIONS.md`. Near-term priorities are:

1. compile and repair the global Fitch knowability boundary;
2. prove independence/minimality of the local Fitch recovery assumptions;
3. add modal satisfaction/validity and formulate full Church-Fitch schemas;
4. classify modal laws of evidence-stable `K` and raw `Diamond`;
5. repair the zero-evidence conditionalization boundary and study dynamic `K`;
6. generalize the structural-transport abstraction across paradox families;
7. deepen Conflict-Nerve topology to homology and persistence;
8. perform a systematic literature/novelty audit before publication claims.

4-PEL is therefore best read as a machine-checkable laboratory for the geometry, dynamics, modal structure, and information loss behind epistemic paradoxes.
