# 4-PEL research question map

Status legend:

- **VERIFIED**: theorem or finite-model claim compiled on the active Lean 4.31 branch.
- **PARTIAL**: a substantial formal answer exists, but the general theorem or literature comparison is incomplete.
- **OPEN**: no satisfactory formal answer yet.
- **INTERPRETIVE**: a working philosophical diagnosis supported by formal results, not itself a machine-checked theorem.

This document separates machine-checked results from open mathematical,
philosophical, semantic, and literature questions.

For the consolidated modal-law picture, see
`docs/MODAL_KNOWLEDGE_CLASSIFICATION.md`.

## A. Questions already answered formally

### A1. Can four-valued knowledge preserve nonclassical information rather than Booleanize it?

**VERIFIED.** On homogeneous accessible profiles, evidence-stable knowledge
recovers the complete FDE value:

```text
homogeneous T -> K(phi) = T
homogeneous F -> K(phi) = F
homogeneous B -> K(phi) = B
homogeneous N -> K(phi) = N
```

Heterogeneous full FDE status forces strict `F`.

This is the current **Knowledge Stability Principle**.

### A2. Is internal negation of knowledge the same as absence of positive knowledge?

**VERIFIED: no.** The repository distinguishes:

```text
meta-level lack of positive knowledge: (K phi).pos = false
negative support for knowledge:       (K phi).neg = true
positive internal not-K:              (not K phi).pos = true
```

These collapse only under additional information-status assumptions. A
reflexive, transitive, Euclidean singleton model with `K phi = N` verifies that
frame geometry alone cannot identify them.

### A3. Does evidence-stable knowledge distribute over conjunction?

**VERIFIED, asymmetrically.** Positive introduction holds:

```text
K+(phi) and K+(psi) -> K+(phi and psi).
```

Positive elimination fails in general. Under `K+(phi and psi)`, the exact left
boundary is:

```text
K+(phi) iff Stable(phi)
```

and analogously for the right conjunct.

At the strict layer, however:

```text
K(phi and psi) = T -> K(phi) = T and K(psi) = T.
```

Thus strict conjunction decomposition survives even though designated
elimination does not.

### A4. Can raw modal possibility be identified with `not K(not phi)`?

**VERIFIED: not globally.** Primitive raw accessibility possibility and the
internal knowledge dual agree exactly when:

```text
Stable(phi) OR Diamond_raw(phi) = T.
```

Under instability, internal dualization can collapse to strict `T`, erasing the
raw four-valued modal profile.

### A5. Can knowledge and raw possibility be represented in one object language conservatively?

**VERIFIED.** `PEL4/ModalLanguage.lean` adds primitive `K` and primitive raw
`Diamond` without changing values of embedded legacy formulas.

### A6. Does the classical Fitch conjunction-extraction step hold for the actual Moorean formula `p and not K p`?

**VERIFIED: no.** A finite object-language model has:

```text
K(p and not K p) = B
K(p)             = F
K(not K p)       = F.
```

The compound is stable while its components are not.

### A7. Which local assumptions restore the Fitch collision?

**VERIFIED.** Positive knowledge of `phi and not K phi` is incompatible with the
local package:

```text
reflexivity
+ Stable(phi)
+ no-glut for K(phi).
```

The repository also contains independent finite witnesses showing the local
role of the recovery assumptions rather than merely one successful model.

### A8. What is the global Church-Fitch boundary in the modal language?

**VERIFIED conditionally.** The modal validity/satisfaction layer, raw
knowability principle, local-to-global recovery theorem, no-gap independence,
strict-truth phase, raw-vs-dual separation, and Church-Fitch classification are
all compiled.

In particular, the positive raw phase verifies a conditional collapse of the
form:

```text
positive raw knowability
+ global source NoGap
+ uniform Fitch recovery
+ global source NoGlut
-> positive omniscience
   and strict-truth positive omniscience
   and strict knowledge omniscience.
```

Strict-truth raw knowability yields the corresponding strict-truth collapse.
Raw possibility and internal dual possibility remain distinct: dualized
knowability can be positive even where witness-bearing raw knowability is not.

### A9. What modal laws does evidence-stable knowledge satisfy?

**VERIFIED for the main factivity/introspection boundaries.** The current
classification is:

```text
probability normalization -> accessibility is nonempty
reflexivity               -> strict factivity
transitivity              -> K+ phi implies value(K K phi) = value(K phi)
Euclideanness alone       -> insufficient for positive internal axiom 5
transitivity + Euclidean  -> K K phi = K phi for all four values
transitivity + Euclidean  -> K(not K phi) = not K phi
NoGap                     -> bridges meta-level ignorance to negative support
```

A finite unrestricted-introspection model verifies that positive axiom 4 fails
without an appropriate frame condition. A separate finite model verifies that
local Euclideanness alone does not suffice for positive internal negative
introspection.

### A10. Does probability normalization constrain the modal frame?

**VERIFIED.** From

```text
mu(R_i(w)) = 1
mu([])     = 0
```

it follows that

```text
R_i(w) != []
```

for every agent and world. Seriality is therefore induced by the probabilistic
model axioms rather than added independently.

### A11. What happens to the Knower fixed point in four values?

**VERIFIED.** The induced map has:

```text
T -> F
F -> T
B -> B
N -> N.
```

The classical values form a two-cycle, while both nonclassical values are fixed
points. Working interpretation: **epistemic fixed-point bifurcation**.

### A12. What is the exact Sorites borderline created by a threshold above one half?

**VERIFIED** in the scaled signed-evidence model. For `c > 50`, the gap interval
is exactly:

```text
100 - c < x < c
```

with width `2c - 100`. The same slack appears as the lower bound on overlap
needed for a glut when both positive and negative evidence cross threshold.

Working interpretation: **Gap--Glut Threshold Duality**.

### A13. What fails in Surprise backward elimination?

**VERIFIED** in the finite model. Each day is predictable only in the special
counterfactual/updated context used to eliminate it, while no day is positively
predicted in the initial model.

Working diagnosis: **context-collapse / prediction-transport failure**.

### A14. How much higher-order Preface conflict structure is invisible to first-order marginals?

**VERIFIED** for the finite incidence formalization. The generic fixed-marginal
fiber has freedom:

```text
2^n - n - 2
```

for `n >= 2`. Full co-conflict data reconstructs exact incidence by Möbius
inversion, while coarse marginals leave exponentially growing interaction
freedom.

### A15. Can identical coarse Preface data support different conflict topology?

**VERIFIED** at the support-nerve/Euler level. Finite profiles with the same
coarse data can realize different simplicial support signatures and Euler
counts. General homology and persistence are not yet formalized.

## B. Questions with a substantial but incomplete answer

### B1. Is the current modal correspondence picture minimal?

**PARTIAL.** Sufficiency and several countermodels are verified, but exact
necessity/minimality is not yet classified for every law.

Examples still worth proving include:

```text
Is local transitivity necessary for positive K-idempotence on the full model class?
What is the weakest condition for full four-value K-idempotence?
Can Euclidean recovery be weakened while preserving K(not K phi) = not K phi?
```

The current theorems establish sharp failures for important weaker conditions,
but not a complete correspondence theorem.

### B2. Is "paradox as structural-transport failure" a genuine common theory?

**PARTIAL / INTERPRETIVE.** The repository verifies distinct transport failures:
projection loss, non-commutation, stability reflection failure, context
transport failure, possibility-duality collapse, threshold phase change,
fixed-point bifurcation, and higher-order interaction loss.

What is still missing is a sufficiently general theorem schema proving that a
family of paradoxical arguments depends on a shared preservation/commutation
property.

### B3. How novel are the combined results?

**OPEN LITERATURE QUESTION.** Individual ingredients have precedents in
Belnap-Dunn logic, paraconsistent epistemic logic, nonstandard knowledge
modalities, Fitch literature, dynamic epistemic logic, threshold belief,
simplicial methods, Möbius inversion, and conflict geometry.

No novelty claim should be made without a systematic comparison of at least:

```text
Knowledge Stability Principle
strict/designated modal phase split
probability-induced seriality
four-valued axiom-4/axiom-5 correspondence pattern
Possibility Duality Collapse
Church-Fitch raw/dual classification
Gap--Glut Threshold Duality
Topological Conflict Underdetermination
paradox-as-structural-transport synthesis
```

### B4. What is the philosophical status of `B` and `N` at the knowledge level?

**PARTIAL / INTERPRETIVE.** The formal distinctions are now precise, but the
epistemological reading remains open. In particular, the project must defend
how to interpret:

```text
K phi = B
K phi = N
meta-level lack of positive knowledge
negative support for K phi
positive internal not K phi
```

without silently importing classical notions of ignorance or contradiction.

## C. High-priority open research questions

### C1. Necessitation and global modal principles

**OPEN.** Classify necessitation-like principles separately for strict truth and
positive/designated truth. Determine which global validity assumptions imply
local or global knowledge and which fail because stability is not preserved.

### C2. Interaction of probabilistic belief `B` and evidence-stable knowledge `K`

**OPEN, high priority.** 4-PEL now has mature separate semantics for both
operators, but their joint logic is largely unexplored.

Questions include:

```text
When does K(phi) imply B(phi)?
Does K(phi) = T force B(phi) = T under current thresholds?
When can B(phi) coexist with K(not phi)?
Can B be glutty where K is strict, or conversely?
What frame/probability assumptions connect the operators?
```

### C3. Dynamic knowledge

**OPEN, high priority.** The Surprise development updates probabilistic belief
models. The modal `K` layer should now be studied under announcement and
evidence update.

Questions include whether update:

```text
preserves accessibility-induced seriality,
preserves or destroys epistemic stability,
creates or removes K-gluts/K-gaps,
changes Fitch recovery conditions,
preserves transitive/Euclidean modal phases.
```

### C4. Repair the zero-evidence conditionalization boundary

**OPEN INFRASTRUCTURE / SEMANTICS.** The current dynamics layer defines a
zero-mass conditionalization fallback but also assumes unconditional
normalization of the conditionalized measure. A principled treatment should
require positive evidence mass or use a safe update subtype.

This should be repaired before strong general dynamic-epistemic theorems are
claimed.

### C5. Algebraic characterization of stability

**OPEN.** Stability is currently semantic over accessible FDE profiles. Research
should seek a more intrinsic algebraic or categorical characterization and
classify which operators preserve or reflect it.

### C6. Global independence/minimality of the Church-Fitch assumptions

**OPEN.** Local recovery assumptions now have finite independence evidence, but
the fully quantified global Church-Fitch packages still deserve an explicit
minimality/independence table.

### C7. General theorem of structural transport

**OPEN, foundational.** Formalize transformations and observations generally
enough to state theorem families of the form:

```text
paradoxical inference requires preservation property P;
finite witness refutes P;
restricted hypotheses recover P.
```

Fitch is currently the clearest worked example.

### C8. Conflict topology beyond Euler signatures

**OPEN.** Add actual simplicial homology, Betti numbers, persistence, and
realizability questions inside fixed-marginal fibers.

### C9. Continuous / measure-theoretic generalization

**OPEN.** Current models are finite and often use exact rational or scaled
integer arithmetic. Determine which results survive on countable or general
probability spaces.

### C10. Automated finite-model search

**OPEN, methodological.** A bounded generator could search FDE valuations,
relations, thresholds, and frame properties for minimal countermodels. The modal
law and Church-Fitch classifications now provide good benchmark targets.

### C11. Literature-grounded modal comparison

**OPEN, publication-critical.** Compare the current primitive `K` semantics and
verified frame laws with nonstandard Belnap-Dunn knowledge modalities and
paraconsistent epistemic systems. The goal is to distinguish genuine new
correspondence results from expected consequences of known semantics.

## D. Suggested research order

The previous Fitch-first sequence is complete enough to retire. A disciplined
near-term sequence is now:

```text
1. consolidate and audit the verified modal-law classification
2. classify interaction between K and probabilistic B
3. prove sharper necessity/minimality results for frame correspondences
4. repair zero-evidence conditionalization
5. study dynamic preservation of K under updates
6. prove global independence/minimality results for Church-Fitch packages
7. expand the structural-transport abstraction across paradox families
8. deepen conflict topology and persistence
9. perform a systematic literature/novelty audit before publication claims
```

The central methodological principle remains to keep four layers distinct:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```

4-PEL is strongest when those layers inform one another without being silently
identified.
