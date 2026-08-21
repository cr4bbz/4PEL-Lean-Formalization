# 4-PEL: Four-Valued Probabilistic Epistemic Logic

4-PEL is a **Lean 4 formalized framework for studying epistemic paradoxes** through the interaction of probabilistic evidence, four-valued semantics, threshold belief, aggregation, self-reference, conflict structure, and information update.

The project began as the formal backbone for *The Cartography of Paradoxes: Unifying Probabilistic Epistemic Logic and Non-Bivalent Validity*. The active research branch now goes substantially beyond that original scope, especially through the Preface conflict-geometry program and a broader investigation of **paradoxes as failures of structural transport**.

> [!IMPORTANT]
> **Research status:** This repository contains a mixture of machine-checked theorems, executable finite models, and explicitly marked research directions. Claims described below as **Lean-verified** have been successfully compiled on the active research branch with Lean 4.31. Interpretive names and broader philosophical theses remain working research terminology unless stated otherwise.

> [!NOTE]
> The paper PDF in the repository should be read as a snapshot of an earlier stage of the project. The current research branch contains results that are not yet incorporated into that manuscript.

---

## Core idea

4-PEL combines a Lockean threshold operator with Belnap-Dunn / First Degree Entailment (FDE). A proposition can occupy one of four states:

| State | Positive support | Negative support | Reading |
| --- | ---: | ---: | --- |
| `T` | yes | no | supported as true |
| `F` | no | yes | supported as false |
| `B` | yes | yes | glut / overdetermination |
| `N` | no | no | gap / underdetermination |

For an agent `i`, world `w`, formula `phi`, and Lockean threshold `c_i`, belief independently thresholds the positive and negative probability mass of `phi`:

```text
B_i(phi).pos  iff  P_pos(phi) >= c_i
B_i(phi).neg  iff  P_neg(phi) >= c_i
```

This allows contradiction to be represented locally as `B` without forcing epistemic explosion, while uncertainty can remain explicitly represented as `N`.

---

## Verified research results

The active branch currently contains the following Lean-verified results.

### 1. Glut Boundary

If positive and negative belief both cross the threshold, a minimum amount of glut mass is unavoidable:

```text
P_B >= 2c - 1
```

In the scaled integer formalization used by several proofs:

```text
P_B >= 2c - 100.
```

This is formalized in `PEL4/Theorems.lean`.

### 2. Lottery and Preface non-agglomeration

The Lottery and Preface models make explicit that threshold belief is not generally closed under conjunction:

```text
B(phi_1), ..., B(phi_n)
```

does not in general imply

```text
B(phi_1 and ... and phi_n).
```

For the symmetric Preface construction, the characteristic threshold boundary is

```text
1/2 < c <= n/(n+1).
```

The Preface configuration is therefore treated as an aggregation problem before it is treated as an object-level contradiction.

### 3. Preface conflict geometry

The Preface project now contains a geometric hierarchy of conflict descriptions.

For nonempty conflict-incidence patterns `A`, let `x_A` denote exact conflict mass and `J_A` the mass shared by all claims in `A`. The full co-conflict hierarchy is a zeta transform of the exact incidence profile:

```text
J_Q = sum_{A superset Q} x_A.
```

A generic Möbius reconstruction theorem recovers every exact incidence mass from the full hierarchy. Thus, at full resolution:

```text
exact incidence x_A
<-> co-conflict hierarchy J_A
<-> weighted conflict filtration f(A).
```

The fixed-carrier / fixed-marginal affine fiber has generic freedom

```text
2^n - n - 2
```

for `n >= 2`.

This gives a quantitative measure of how much higher-order conflict structure is invisible to first-order marginals.

### 4. Conflict Nerve

For a query `A`, define support by positive co-conflict mass:

```text
A is in the support Conflict Nerve  iff  J_A > 0.
```

Antitonicity of co-conflict ensures downward closure, so thresholded co-conflict families form simplicial complexes. The filtration

```text
f(A) = d - J_A
```

is face/coface monotone and exactly recovers the co-conflict hierarchy by

```text
J_A = d - f(A).
```

In the three-claim fixed-marginal fiber, Lean verifies profiles with identical coarse data but different support-nerve signatures and Euler counts:

```text
edge + isolated vertex     chi = 2
triangle boundary          chi = 0
filled triangle            chi = 1
```

This establishes a finite combinatorial form of **topological conflict underdetermination**. A full simplicial-homology formalization is a later target; the current Lean layer verifies the support signatures and Euler counts.

### 5. Knower fixed-point bifurcation

`PEL4/Paradoxes/Knower.lean` studies the self-referential map induced by the schematic Knower equation

```text
K := not B(K)
```

inside the actual 4-PEL evaluator. Lean verifies the complete four-valued dynamics:

```text
T -> F
F -> T
B -> B
N -> N
```

Hence:

```text
knowerStep(v) = v  iff  v = B or v = N.
```

The two nonclassical values are stable fixed points, while the classical values form a two-cycle. This motivates the working phrase **epistemic fixed-point bifurcation**.

### 6. Sorites threshold geometry

`PEL4/Paradoxes/Sorites.lean` studies exclusive signed evidence on a 0--100 scale:

```text
positive = x
negative = 100 - x.
```

For `c > 50`, Lean verifies that the gappy borderline region is exactly

```text
100 - c < x < c,
```

with algebraic width

```text
2c - 100.
```

The same threshold slack appears in the Glut Boundary as the minimum overlap mass required when positive and negative support both reach threshold. This is the formal core of the working **Gap--Glut Threshold Duality**:

```text
exclusive evidence  -> gap width = 2c - 100
overlapping evidence -> required glut mass >= 2c - 100.
```

The theorem concerns signed-evidence threshold geometry; interpreting that geometry as a model of vagueness is a philosophical application rather than part of the formal result.

### 7. Surprise Examination: dynamic reversal and context transport

The Surprise model uses the repository's existing `conditionalize` machinery on three initially equiprobable exam days with threshold `2/3`.

Successive evidence updates produce the verified trajectory

```text
belief(exam Friday):      F -> N -> T
belief(not exam Friday):  T -> N -> F.
```

Thus adding truthful information can first remove categorical determination and then reverse it.

The backward-elimination extension proves a second and stronger result. Friday, Wednesday, and Monday are each positively predictable in the special updated or counterfactual context used to eliminate that day, while none is positively predicted in the initial model:

```text
predictable(day, elimination-context(day)) = true
predictable(day, initial-model)             = false.
```

The formal diagnosis is therefore not merely non-monotonic belief update. It isolates a **context-transport failure**: predictions licensed in distinct epistemic contexts do not automatically transport back to the initial context.

---

## Paradox map

A current working taxonomy is:

| Paradox / family | Structural pressure point | Current 4-PEL diagnosis | Status |
| --- | --- | --- | --- |
| Lottery | thresholding vs conjunction | non-commutation | Lean-verified model |
| Preface | local acceptance vs global interaction | projection loss / fiber underdetermination | Lean-verified research program |
| Moore | truth vs belief status | level separation | executable model |
| Liar | self-reference + contradiction | glut-compatible behavior without explosion | executable model + ex-falso theorem |
| Knower | epistemic self-reference | nonclassical fixed-point bifurcation | Lean-verified |
| Sorites | gradual evidence vs categorical status | threshold gap/glut geometry | Lean-verified |
| Surprise Examination | update and backward elimination | dynamic reversal + context transport failure | Lean-verified |
| Fitch | knowability vs actual knowledge | modal-epistemic transport | planned; requires new operators |

This motivates the active research thesis:

## Paradoxes as failures of structural transport

The earlier heuristic, **paradoxes as projection errors**, explains the Lottery and Preface cases but is too narrow. A broader pattern is that paradoxical reasoning often presupposes that an epistemically important property survives some transformation.

Schematically:

```text
rich structure E  --T-->  transformed structure E'
     |                         |
     pi                        pi
     v                         v
coarse state S  --T*-->   coarse state S'
```

A paradoxical inference may behave as if

```text
pi(T(E)) = T*(pi(E))
```

must hold. 4-PEL lets us ask whether it actually does.

The repository currently exhibits several distinct failure modes:

- projection loss,
- non-commutation,
- nonclassical fixed points,
- threshold phase changes,
- dynamic status reversal,
- context-indexed transport failure,
- higher-order interaction loss.

This is an active research program rather than a finished universal theory of paradoxes. See `docs/PARADOX_TRANSPORT_RESEARCH.md` for the current argument and open questions.

---

## Architecture

Core formalization:

- `PEL4/FDE.lean` — four-valued algebra and connectives
- `PEL4/Model.lean` — finite epistemic models and probability measures
- `PEL4/Belief.lean` — Lockean threshold belief
- `PEL4/Syntax.lean` — object language and evaluator
- `PEL4/Theorems.lean` — core boundary results
- `PEL4/Soundness.lean`, `PEL4/ExFalso.lean` — semantic consequence and paraconsistency
- `PEL4/Dynamics.lean` — evidence conditionalization
- `PEL4/ActionModel.lean`, `PEL4/ProductUpdate.lean` — dynamic/product-update machinery
- `PEL4/Diagnostics.lean` — glut/gap/determination diagnostics
- `PEL4/ReliableEvidence.lean`, `PEL4/Revision.lean` — experimental reliability and revision layers

Paradox and research modules:

- `PEL4/Paradoxes/Lottery.lean`
- `PEL4/Paradoxes/Preface*.lean`
- `PEL4/Paradoxes/Moore.lean`
- `PEL4/Paradoxes/Liar.lean`
- `PEL4/Paradoxes/Knower.lean`
- `PEL4/Paradoxes/Sorites.lean`
- `PEL4/Paradoxes/SurpriseExamination.lean`
- `PEL4/Paradoxes/SurpriseBackwardElimination.lean`
- `PEL4/Paradoxes/Cartography.lean`
- `PEL4/Paradoxes/SyntheseExtensions.lean`

Research notes:

- `docs/PARADOX_TRANSPORT_RESEARCH.md` — cross-paradox structural-transport program
- `docs/CONFLICT_NERVE_RESEARCH.md` — Conflict Nerve, Dowker, persistence direction
- Preface-specific source modules under `PEL4/Paradoxes/Preface*` contain the machine-checked geometric development

---

## Visualizations

The `visualization/` directory contains lightweight Python / Matplotlib companions for the geometric research:

```text
conflict_triangle.py    coarse conflict-triangle geometry
fiber_tetrahedron.py    three-claim fixed-marginal tetrahedral fiber
dimension_growth.py     growth of visible vs hidden conflict degrees
conflict_nerve.py       support-nerve examples and threshold views
```

Install the optional visualization dependency with:

```bash
python -m pip install -r visualization/requirements.txt
```

Example runs:

```bash
python visualization/conflict_nerve.py
python visualization/fiber_tetrahedron.py --m 6
python visualization/dimension_growth.py --max-n 12
```

The visualization layer is explanatory tooling; the Lean theorems do not depend on Matplotlib.

---

## Build and verification

The Lean project intentionally avoids a Mathlib dependency. Finite models use exact rational probabilities where convenient, while several generic inequalities use scaled integer encodings so they can be discharged with Lean's built-in arithmetic tooling such as `omega`.

For the active research branch:

```bash
git clone https://github.com/cr4bbz/4PEL-Lean-Formalization.git
cd 4PEL-Lean-Formalization
git checkout research/preface-case-study
lake build
```

A successful `lake build` checks every module imported by `PEL4.lean`.

The absence of Mathlib is an implementation choice for a small and inspectable formal core, not a claim that continuous measure-theoretic generalizations are unnecessary. Some geometric statements are currently proved in finite or scaled form and may later be generalized.

---

## Research boundaries

Several distinctions are kept explicit to avoid overclaiming:

- `B_i(phi)` is probabilistic threshold belief, not automatically factive knowledge.
- Internal FDE negation `not B_i(phi)` is not identical to the meta-level absence of positive belief in `phi`.
- The current Liar and Gödel-inspired modules model nonclassical fixed behavior; they are not complete formalizations of semantic diagonalization or Gödel's incompleteness theorem.
- Conflict-Nerve support signatures and Euler counts are formalized; general simplicial homology and persistence are not yet part of the Lean core.
- The Surprise modules formalize belief-threshold dynamics and backward context transport, not the complete factive knowledge formulation of the classical puzzle.
- A faithful Fitch development is deferred until knowledge, knowability / possibility, factivity, and epistemic-status absence are represented explicitly.

These boundaries are deliberate. The project aims to distinguish **theorem, model, interpretation, and research conjecture** rather than collapse them into one layer.

---

## Current research direction

The next major questions are:

1. Which paradoxes can be characterized by a common structural-transport failure, and which resist that taxonomy?
2. How should knowledge `K`, probabilistic belief `B`, modal possibility, and absence of epistemic support be separated for a faithful Fitch analysis?
3. Which support-nerve topologies and persistence signatures are realizable inside a fixed-marginal conflict fiber?
4. How much interaction order is required to determine a chosen topological or epistemic invariant?
5. Can the finite signed-threshold results be lifted cleanly to more general probabilistic / measure-theoretic settings?

The repository is therefore best read not only as an implementation of one logic, but as a machine-checkable laboratory for the geometry, dynamics, and information loss behind epistemic paradoxes.
