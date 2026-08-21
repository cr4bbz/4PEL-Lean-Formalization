# 4-PEL research question map

Status legend:

- **VERIFIED**: theorem or finite-model claim compiled on the active Lean 4.31 branch.
- **PARTIAL**: a substantial formal answer exists, but the general theorem or literature comparison is incomplete.
- **OPEN**: no satisfactory formal answer yet.
- **INTERPRETIVE**: a working philosophical diagnosis supported by formal results, not itself a machine-checked theorem.

This document separates what the project can already answer from what still
requires mathematical, logical, philosophical, or literature research.

## A. Questions already answered formally

### A1. Can four-valued knowledge preserve nonclassical information rather than Booleanize it?

**VERIFIED.** The evidence-stable knowledge candidate returns all four FDE values
on homogeneous accessible profiles:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N
```

Heterogeneous full FDE status forces the candidate to strict `F`.

This gives a precise **Knowledge Stability Principle**: homogeneous accessible
status is recovered, while full-value heterogeneity counts against knowledge.

### A2. Is internal negation of knowledge the same as absence of positive knowledge?

**VERIFIED.** They coincide exactly when the knowledge value is classical.
At `B` and `N`, internal FDE negation and meta-level absence of positive support
diverge.

Hence one cannot silently read

```text
not K(phi)
```

as

```text
phi is not positively known.
```

throughout a four-valued model.

### A3. Does positive evidence-stable knowledge distribute over conjunction?

**VERIFIED, directionally.** Introduction holds:

```text
K+(phi) and K+(psi) -> K+(phi and psi).
```

Unrestricted elimination fails:

```text
K+(phi and psi) -/-> K+(phi).
```

Under the premise `K+(phi and psi)`, the exact left-elimination boundary is:

```text
K+(phi) iff Stable(phi).
```

and analogously for the right conjunct.

Thus composition preserves epistemic stability, while decomposition need not
reflect it.

### A4. Can raw modal possibility be identified with `not K(not phi)`?

**VERIFIED: not globally.** Primitive raw accessibility possibility and the
internal knowledge dual diverge on unstable four-valued profiles.

The exact boundary is:

```text
Diamond_raw(phi) = not K(not phi)
iff
Stable(phi) OR Diamond_raw(phi) = T.
```

The second disjunct is accidental extensional agreement: under instability the
internal dual collapses to strict `T`, so equality survives only if raw
possibility was already `T`.

### A5. Can knowledge and raw possibility be represented in one object language without breaking the old 4-PEL core?

**VERIFIED.** `PEL4/ModalLanguage.lean` adds a conservative modal language with
primitive `K` and primitive raw `Diamond`. Every legacy formula embeds without
changing semantic value.

### A6. Does the classical Fitch conjunction-extraction step hold for the actual Moorean formula `p and not K p`?

**VERIFIED: no.** There is a finite object-language model with a reflexive
critical witness where:

```text
K(p and not K p) = B
K(p)             = F
K(not K p)       = F.
```

The compound is stable while its components are not. Thus the classical move

```text
K+(p and not K p) -> K+(p)
```

fails in exactly the Fitch-shaped formula, not merely for two independent
conjuncts.

### A7. Which local assumptions restore the classical Fitch collision?

**VERIFIED.** At a point with positive knowledge of `phi and not K phi`, the
following package is inconsistent:

```text
reflexivity
+ Stable(phi)
+ no-glut condition for K(phi).
```

Reflexivity gives factivity of the known Moorean conjunction; stability restores
extraction to `K(phi)`; the no-glut condition makes simultaneous positive and
negative support for `K(phi)` impossible.

The current Fitch countermodel satisfies reflexivity and local no-glut, but
violates `Stable(p)`. Thus its concrete escape route is specifically component
instability.

### A8. What happens to the Knower fixed point in four values?

**VERIFIED.** The induced map has:

```text
T -> F
F -> T
B -> B
N -> N.
```

The classical values form a two-cycle, while both nonclassical values are fixed
points. Working interpretation: **epistemic fixed-point bifurcation**.

### A9. What is the exact Sorites borderline created by a threshold above one half?

**VERIFIED** in the scaled signed-evidence model. For `c > 50`, the gap interval
is exactly:

```text
100 - c < x < c
```

with width `2c - 100`. The same slack appears as the lower bound on overlap
needed for a glut when both positive and negative evidence cross threshold.

Working interpretation: **Gap--Glut Threshold Duality**.

### A10. What fails in Surprise backward elimination?

**VERIFIED** in the finite model: each day is predictable in the special
counterfactual/updated context used to eliminate it, while no day is positively
predicted in the initial model.

Thus branch-relative predictions do not transport back to the initial context.
Working diagnosis: **context-collapse / prediction-transport failure**.

### A11. How much higher-order Preface conflict structure is invisible to first-order marginals?

**VERIFIED** for the finite incidence formalization. The generic fixed-marginal
fiber has freedom:

```text
2^n - n - 2
```

for `n >= 2`. Full co-conflict data reconstructs exact incidence by Möbius
inversion, while coarse marginals leave exponentially growing interaction
freedom.

### A12. Can identical coarse Preface data support different conflict topology?

**VERIFIED** at the support-nerve/Euler level. Finite profiles with the same
coarse data can realize different simplicial support signatures and Euler
counts. General homology and persistence are not yet formalized.

## B. Questions with a substantial but incomplete answer

### B1. What is the global Fitch knowability boundary?

**PARTIAL / CURRENT BUILD GATE.** The new
`PEL4/Paradoxes/FitchKnowabilityBoundary.lean` targets the theorem:

```text
Diamond_raw+ K(phi and not K phi)
-> there exists an accessible positive knowledge witness
   that violates the local Fitch recovery package.
```

A stronger corollary says that if every accessible candidate witness is
reflexive, `phi`-stable, and no-glut for `K(phi)`, then positive raw Fitch
knowability is impossible.

This module is not marked verified until a successful local `lake build` is
reported.

### B2. Is the local Fitch recovery package genuinely minimal?

**PARTIAL.** The present finite Fitch model shows that dropping component
stability can allow the Moorean knowledge witness while reflexivity and no-glut
remain intact.

Still missing are independent witnesses or theorems showing what happens when:

```text
reflexivity alone is dropped,
no-glut alone is dropped,
stability alone is dropped,
and combinations of two assumptions are dropped.
```

A proper independence theorem would turn the current candidate-minimal package
into a proved minimal package.

### B3. Does 4-PEL refute Fitch's theorem, or only block one classical derivation?

**PARTIAL.** The repository now verifies a Fitch-shaped countermodel to
unrestricted knowledge-conjunction extraction and a local recovery theorem.
That is not yet a full theorem about Church-Fitch knowability.

The standard theorem schema quantifies over truths and uses a knowability
principle. 4-PEL still needs a formal validity/satisfaction layer for the modal
language and an explicit schema corresponding to something like:

```text
if phi is true/designated, then Diamond K(phi).
```

Only then can the project distinguish:

```text
failure of a standard proof,
failure of the theorem under 4-PEL semantics,
and recovery of the theorem on restricted fragments.
```

### B4. Is "paradox as structural-transport failure" a genuine common theory?

**PARTIAL / INTERPRETIVE.** The repository now contains several formally distinct
failures that fit the transport language: projection loss, non-commutation,
stability reflection failure, context transport failure, duality collapse,
threshold phase change, and fixed-point bifurcation.

What is not yet proved is a common abstract theorem saying when such failures
generate a paradoxical argument. The current thesis is a research program, not
a universal theorem.

### B5. How novel are the combined results?

**OPEN LITERATURE QUESTION.** Individual ingredients have clear precedents in
Belnap-Dunn logic, paraconsistent epistemic logic, nonstandard knowledge
modalities, Fitch literature, dynamic epistemic logic, threshold belief,
simplicial methods, Möbius inversion, and conflict geometry.

A systematic literature review is required before claiming novelty for:

```text
Knowledge Stability Principle,
Stability Reflection Boundary,
Possibility Duality Collapse,
local/global Fitch transport boundary,
Gap--Glut Threshold Duality,
Topological Conflict Underdetermination,
paradox-as-structural-transport synthesis.
```

## C. High-priority open research questions

### C1. Full Church-Fitch theorem schema in the modal language

**OPEN, highest priority after the global boundary gate.** Define designated
truth and model/global validity for `ModalFormula`, formulate alternative
knowability principles, and prove exactly which combinations imply omniscience,
contradiction, glut, or non-collapse.

Important variants include:

```text
strict-T truth versus merely positive/designated truth,
raw Diamond versus the internal dual not K not,
local versus global knowability,
formula-wide versus restricted-fragment knowability.
```

### C2. Independence of the Fitch recovery assumptions

**OPEN, high priority.** Construct finite countermodels or general theorems for
each omitted assumption. The goal is an actual independence/minimality table,
not just one successful countermodel.

### C3. Modal laws of evidence-stable knowledge

**OPEN.** Characterize exactly which familiar modal principles survive:

```text
K distribution laws,
positive and negative introspection,
necessitation-like principles,
K K phi versus K phi,
factivity under frame conditions,
interaction between K and probabilistic B.
```

Frame correspondences should be proved where possible rather than assumed.

### C4. Algebraic characterization of stability

**OPEN.** Stability is currently a semantic predicate over accessible FDE
profiles. Research should ask whether there is a more intrinsic algebraic or
categorical characterization and which connectives preserve or reflect it.

Conjunction already shows an important asymmetry:

```text
component stability -> compound stability,
compound stability -/-> component stability.
```

The same question should be asked for negation, disjunction, implication,
belief, knowledge, and dynamic update.

### C5. Dynamic knowledge rather than only dynamic threshold belief

**OPEN.** The Surprise development updates probabilistic belief models. The new
object-language `K` makes it possible to study public announcements and evidence
updates with evidence-stable knowledge itself.

Questions include whether update preserves stability, creates/destroys
knowledge gluts, or changes the Fitch recovery package.

### C6. Repair the zero-evidence conditionalization boundary

**OPEN INFRASTRUCTURE / SEMANTICS.** The current dynamics layer defines a
zero-mass conditionalization fallback but assumes unconditional normalization of
the conditionalized measure. A principled treatment should either require
positive evidence mass or use a safe update subtype.

This matters before making strong general dynamic-epistemic claims.

### C7. Interaction of probability thresholding and evidence-stable knowledge

**OPEN.** 4-PEL now has both `B` and `K`, but their interaction is largely
unexplored. Questions include:

```text
When does K(phi) imply B(phi)?
When can B(phi) coexist with K(not phi)?
Can threshold changes destroy or create knowledge stability indirectly?
What are the joint B/K fixed points?
```

### C8. General theorem of structural transport

**OPEN, foundational.** Formalize transformations and observations sufficiently
generally to express multiple paradoxes in one theorem family. Candidate
components already exist in `PEL4/StructuralTransport.lean`.

The target is not a slogan but statements of the form:

```text
paradoxical inference requires preservation/commutation property P;
finite witness refutes P;
restricted hypotheses recover P.
```

Fitch is currently the clearest worked example of this three-stage pattern.

### C9. Conflict topology beyond Euler signatures

**OPEN.** Add actual simplicial homology, Betti numbers, persistence, and
realizability questions inside fixed-marginal fibers.

Central questions:

```text
Which complexes can occur as conflict nerves?
Which filtrations are realizable by nonnegative incidence data?
How much interaction order determines Betti numbers or persistence bars?
```

### C10. Continuous / measure-theoretic generalization

**OPEN.** Current models are finite and often use exact rational or scaled
integer arithmetic. Determine which theorems survive for countable or general
probability spaces and which rely essentially on finiteness.

### C11. Automated finite-model search

**OPEN, methodological.** Many important discoveries came from hand-designed
finite witnesses. A bounded model generator could search FDE valuations,
accessibility relations, thresholds, and structural conditions for minimal
countermodels.

This would be especially valuable for Fitch-assumption independence and modal
law classification.

### C12. Philosophical interpretation of `B` and `N` at the knowledge level

**OPEN / INTERPRETIVE.** The semantics permits both glutty and gappy knowledge.
The project should distinguish at least:

```text
conflicting evidence that still counts as knowledge,
underdetermined evidence that counts as gappy knowledge,
meta-level ignorance,
internal epistemic negation,
absence of positive knowledge.
```

The formal distinctions are increasingly clear; the epistemological reading
still needs sustained philosophical argument.

## D. Suggested research order

A disciplined near-term sequence is:

```text
1. compile and repair FitchKnowabilityBoundary
2. prove independence/minimality of the local Fitch package
3. add modal satisfaction/validity and formal Church-Fitch schemas
4. classify the resulting Fitch theorem variants
5. characterize broader modal laws of K and Diamond
6. repair dynamic conditionalization and study dynamic K
7. expand structural-transport abstraction across paradox families
8. deepen conflict topology and persistence
9. perform a systematic novelty/literature audit before publication claims
```

The central methodological principle is to keep four layers distinct:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```

4-PEL is strongest when those layers inform one another without being silently
identified.
