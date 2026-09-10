# 4-PEL: Four-Valued Probabilistic Epistemic Logic

4-PEL is a **Lean 4 formalized framework for studying epistemic paradoxes** through the interaction of probabilistic evidence, four-valued semantics, threshold belief, evidence-stable knowledge, modal possibility, aggregation, self-reference, conflict structure, and information update.

The project began as the formal backbone for *The Cartography of Paradoxes: Unifying Probabilistic Epistemic Logic and Non-Bivalent Validity*. The active research branch now goes substantially beyond that original scope, especially through the Preface conflict-geometry program, a four-valued modal knowledge/knowability layer, and a broader investigation of **paradoxes as failures of structural transport**.

> [!IMPORTANT]
> **Research status:** This repository contains machine-checked theorems, executable finite models, and explicitly marked research directions. Claims described as **Lean-verified** have compiled successfully on the active research branch with Lean 4.31. Interpretive names and broader philosophical theses remain working research terminology unless stated otherwise.

> [!NOTE]
> `paper/main.pdf` is the current 54-page working-manuscript snapshot for this
> branch. Results developed only on independent research branches are not
> included unless they have been explicitly integrated.

The current development baseline is
`research/recovery-observation-sites-gate21`. Start with
[`docs/REPOSITORY_MAP.md`](docs/REPOSITORY_MAP.md) for the repository layout,
gate sequence, verification entry points, and independent branch boundaries.

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
at `N`.

Gate 3 instantiates that contract on a four-level ordered welfare carrier. Lean
checks the probability side conditions uniformly for every admissible `k` and
an explicit two-step path `0 -> p -> p+p=1`. A concrete population kernel maps
its endpoint outcomes to pure `N`/`B` evidence, so the path begins at a gap and
ends at classical conflict with 4-PEL value `B`. Constructing the chain also
exposes anonymity as structural: successive list representations compose only
up to population permutation. The move relation is still syntactically
generated, not yet derived from a substantive axiology. A focused axiom audit
is compiled in CI. See
`docs/FINITE_FINE_GRAINEDNESS_4PEL.md` for hypotheses and formalization limits.

### 14. Matroid evidence, circuits, and minors

The current research line represents positive and negative evidence channels
through a finite matroid-style closure interface. Lean verifies the channel
closure model, its FDE realization, the classification of channel circuits,
circuit elimination, and deletion/contraction semantics. Parallel deletion can
preserve a channel, while deleting its unique representative destroys support;
contraction separates visible occupancy from residual nonloop capacity.

### 15. Structural and formula-level classical recovery

Classical values are recovered internally rather than postulated globally:

```text
complete evidence + consistent evidence
iff
FDE value is T or F.
```

The recovered slice is closed under propositional negation, conjunction, and
disjunction. Atomic classicality propagates through the propositional fragment,
but does not by itself force threshold belief to be classical. Belief and modal
recovery therefore require their own profile and threshold hypotheses.

### 16. Lockean threshold phase boundary

For complementary classical support masses, the threshold regime determines
which nonclassical defect remains possible. At-most-half thresholds exclude
gaps but allow gluts; supermajority thresholds exclude gluts but allow gaps.
Probability integrity plus threshold completeness gives the exact recovery
condition for classical belief.

### 17. CPEL split representation and collapse

The positive and negative translations recover the two FDE support bits exactly.
Every 4-PEL evaluation is therefore represented by an induced Boolean pair. On
the classical anti-diagonal the two coordinates become complements, and the
representation collapses to one Boolean bit. LP and ST consequence also admit
exact translations into this model-induced CPEL evaluator.

### 18. Recovery transfer to laws and consequence

Gate 9 transfers local recovery to logical laws and restricted consequence:

```text
tolerant LEM     iff gap-free
universal LP EFQ iff glut-free
strict LEM       iff classical
classical        iff tolerant LEM and universal LP EFQ.
```

ST and LP consequence coincide when restricted to evaluations with a classical
antecedent. This is not unrestricted global classical consequence: an explicit
finite countermodel still refutes global LP explosion. See
[`docs/RECOVERY_CONSEQUENCE_TRANSFER_GATE9.md`](docs/RECOVERY_CONSEQUENCE_TRANSFER_GATE9.md).

### 19. Compositional modal recovery

Gate 10 introduces a recursive recovery contract for the full `ModalFormula`
language. Propositional constructors preserve recovery; knowledge and raw
possibility require recovery throughout the accessible profile; threshold
belief additionally requires threshold completeness. Under probability
integrity, every recovered modal formula evaluates classically. A globally
recovered antecedent then makes model-relative ST and LP consequence coincide.
The Gate-6 threshold-gap witness confirms that classical atoms alone still do
not recover belief. See
[`docs/COMPOSITIONAL_CLASSICAL_RECOVERY_GATE10.md`](docs/COMPOSITIONAL_CLASSICAL_RECOVERY_GATE10.md).

### 20. Dynamic compositional recovery

Gate 11 connects the recovery contract to admissible conditionalization. Given
prior recovery, posterior recovery holds exactly when every reachable belief
node remains threshold-complete after the update. Threshold-side robustness
also preserves classical antecedent evaluation and therefore the model-relative
ST/LP collapse. Existing finite models now prove both recovery fracture
(`T/T/T -> T/N/T`) and recovery restoration (`T/N/T -> T/T/T`), so the dynamic
behavior is non-monotone. See
[`docs/DYNAMIC_COMPOSITIONAL_RECOVERY_GATE11.md`](docs/DYNAMIC_COMPOSITIONAL_RECOVERY_GATE11.md).

### 21. Directional threshold-wall recovery

Gate 12 orients the existing threshold walls. Every support coordinate either
stays below, rises, falls, or stays above threshold. From a prior classical
belief, `T -> N` and `F -> N` are exactly downward loss patterns, while
`T -> B` and `F -> B` are exactly upward conflict patterns. A prior gap becomes
complete exactly when at least one support side rises. The classification lifts
recursively: prior recovery plus probability integrity makes posterior recovery
equivalent to the absence of a directed gap pattern at every reachable belief
node. See
[`docs/DIRECTIONAL_THRESHOLD_RECOVERY_GATE12.md`](docs/DIRECTIONAL_THRESHOLD_RECOVERY_GATE12.md).

### 22. Probability integrity under conditionalization

Gate 13 proves that no additional update axioms are needed to preserve the
strong finite-probability contract. On a probability-integrity prior, the
existing admissibility structure is equivalent to positive local evidence mass
alone; its empty- and total-mass obligations are derivable. Every admissible
conditionalization therefore remains probability-integrity-certified.

This closes the Gate-12 boundary: for a previously recovered formula, absence
of reachable directed gaps is exactly recursive semantic classicality in the
posterior model. It also restores the model-relative ST/LP coincidence without
requiring full value invariance. See
[`docs/CONDITIONALIZATION_PROBABILITY_INTEGRITY_GATE13.md`](docs/CONDITIONALIZATION_PROBABILITY_INTEGRITY_GATE13.md).

### 23. Recursive LEM/EFQ characterization

Gate 14 lifts tolerant excluded middle and universal LP explosion from a single
value to every subformula and accessible modal operand. Lean proves that this
recursive law profile is exactly `CompositionallyClassical`; with probability
integrity it is also exactly the compositional recovery certificate. See
[`docs/RECURSIVE_CLASSICAL_LAW_PROFILE_GATE14.md`](docs/RECURSIVE_CLASSICAL_LAW_PROFILE_GATE14.md).

### 24. Maximal recursive classical fragment

Gate 15 proves that `CompositionallyClassicalAt` is the greatest fragment among
candidate predicates required to satisfy the complete recursive LEM/EFQ
traversal. Finite witnesses show that each law axis is independently necessary
and that root-level classicality can mask a nonclassical subformula. See
[`docs/MAXIMAL_CLASSICAL_LAW_FRAGMENT_GATE15.md`](docs/MAXIMAL_CLASSICAL_LAW_FRAGMENT_GATE15.md).

### 25. Independent classical modal semantics

Gate 16 adds a genuinely separate Boolean probabilistic-epistemic model and
evaluator, with ordinary universal knowledge and existential possibility.
Projection from 4-PEL preserves and reflects the complete formula value exactly
on the recovered sector. See
[`docs/INDEPENDENT_CLASSICAL_MODAL_SEMANTICS_GATE16.md`](docs/INDEPENDENT_CLASSICAL_MODAL_SEMANTICS_GATE16.md).

### 26. Recovered classical consequence equivalence

Gate 17 proves truth preservation and reflection and a model-relative
conservativity theorem: for recovered antecedent and consequent, 4-PEL LP
consequence agrees with ordinary consequence in the independent classical
model. Under probability integrity, ST, LP, and classical consequence coincide
on that sector. This is not an unrestricted collapse or a proof-system
completeness theorem. See
[`docs/RECOVERED_CLASSICAL_CONSEQUENCE_EQUIVALENCE_GATE17.md`](docs/RECOVERED_CLASSICAL_CONSEQUENCE_EQUIVALENCE_GATE17.md).

### 27. Independent classical-calculus soundness

Gate 18 introduces a separate classical derivability relation with
propositional rules and monotonicity rules for knowledge, possibility, and
threshold belief. Lean proves soundness over independent classical models with
finite probability integrity and transports every such derivation to LP and ST
consequence in the recovered 4-PEL sector. A finite weak-measure witness shows
why probability integrity is necessary for belief monotonicity. Completeness
and decidability remain open. See
[`docs/CLASSICAL_MODAL_CALCULUS_SOUNDNESS_GATE18.md`](docs/CLASSICAL_MODAL_CALCULUS_SOUNDNESS_GATE18.md).

### 28. Recovery along finite update sequences

Gate 19 represents admissible conditionalizations as dependent finite traces.
For an initially recovered formula, recovery at every later state is equivalent
to excluding directed gap creation on every edge; every failure therefore has
an earliest directed-gap witness. A four-world two-update model additionally
realizes `T -> N -> T`, proving that final recovery need not mean uninterrupted
recovery. See
[`docs/FINITE_UPDATE_RECOVERY_GATE19.md`](docs/FINITE_UPDATE_RECOVERY_GATE19.md).

### 29. Finite local evidence-scope bounds

Gate 20 compiles each dependent update trace into the cumulative evidence
scope at a fixed agent/world belief site. Lean proves the sharp resource bound
`final scope size + strict shrink count <= initial scope size`; the Gate-19
loss-and-return trace has two such strict local shrinkages. This is not yet a
global bound on recovery flips, because that requires a finite compiler for all
formula-reachable belief sites and a recovery-stuttering theorem. See
[`docs/FINITE_UPDATE_SCOPE_BOUNDS_GATE20.md`](docs/FINITE_UPDATE_SCOPE_BOUNDS_GATE20.md).

### 30. Finite recovery-observation maps

Gate 21 compiles the exact finite list of semantic observations used by the
recursive recovery certificate on explicit starting worlds. The list is
structurally invariant under conditionalization, and Lean proves a stuttering
theorem: if every entry keeps its classical/nonclassical status, recovery
cannot change. Since atomic entries always stutter, every recovery change has
a concrete changed belief-result witness in the finite list. A coverage proof lifts the result to globally quantified
recovery. See
[`docs/FINITE_REACHABLE_RECOVERY_GATE21.md`](docs/FINITE_REACHABLE_RECOVERY_GATE21.md).

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
| Population axiology | finite small-step chains + reciprocal-risk interpolation | permutation-invariant path composition; normalized evidence-kernel lift to non-trivial `B` | Lean-verified Gate 3 instance |

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

Current recovery-track modules include:

```text
PEL4/MatroidEvidence.lean
PEL4/MatroidEvidenceCircuits.lean
PEL4/MatroidEvidenceMinors.lean
PEL4/ClassicalRecovery.lean
PEL4/FormulaClassicalRecovery.lean
PEL4/ModalFormulaClassicalRecovery.lean
PEL4/LockeanThresholdPhaseTransition.lean
PEL4/ProbabilityIntegrityFormulaRecovery.lean
PEL4/CPELClassicalCollapse.lean
PEL4/CPELConsequenceBridge.lean
PEL4/RecoveryConsequenceTransfer.lean
PEL4/CompositionalClassicalRecovery.lean
PEL4/DynamicCompositionalRecovery.lean
PEL4/DirectionalThresholdRecovery.lean
PEL4/ConditionalizationProbabilityIntegrity.lean
PEL4/RecursiveClassicalLawProfile.lean
PEL4/MaximalClassicalLawFragment.lean
PEL4/IndependentClassicalModalSemantics.lean
PEL4/RecoveredClassicalConsequenceEquivalence.lean
PEL4/ClassicalModalCalculus.lean
PEL4/FiniteUpdateRecovery.lean
PEL4/FiniteUpdateScopeBounds.lean
PEL4/FiniteReachableRecovery.lean
```

Research notes:

```text
docs/REPOSITORY_MAP.md
docs/FINITE_REACHABLE_RECOVERY_GATE21.md
docs/PAPER_REVIEW_GATE21.md
docs/FINITE_UPDATE_SCOPE_BOUNDS_GATE20.md
docs/PAPER_REVIEW_GATE20.md
docs/FINITE_UPDATE_RECOVERY_GATE19.md
docs/PAPER_REVIEW_GATE19.md
docs/CLASSICAL_MODAL_CALCULUS_SOUNDNESS_GATE18.md
docs/RECOVERED_CLASSICAL_CONSEQUENCE_EQUIVALENCE_GATE17.md
docs/PAPER_REVIEW_GATE17.md
docs/INDEPENDENT_CLASSICAL_MODAL_SEMANTICS_GATE16.md
docs/MAXIMAL_CLASSICAL_LAW_FRAGMENT_GATE15.md
docs/RECURSIVE_CLASSICAL_LAW_PROFILE_GATE14.md
docs/CONDITIONALIZATION_PROBABILITY_INTEGRITY_GATE13.md
docs/DIRECTIONAL_THRESHOLD_RECOVERY_GATE12.md
docs/PAPER_REVIEW_GATE12.md
docs/DYNAMIC_COMPOSITIONAL_RECOVERY_GATE11.md
docs/COMPOSITIONAL_CLASSICAL_RECOVERY_GATE10.md
docs/RECOVERY_CONSEQUENCE_TRANSFER_GATE9.md
docs/CPEL_CLASSICAL_COLLAPSE_GATE8.md
docs/CLASSICAL_RECOVERY_GATE5.md
docs/MATROID_EVIDENCE.md
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
git checkout research/recovery-observation-sites-gate21
lake build
```

A successful `lake build` checks every module imported by `PEL4.lean`. The
separate manuscript, MPFG, and population-axiology audit surfaces are exercised
by CI; exact commands and exclusions are listed in
[`docs/REPOSITORY_MAP.md`](docs/REPOSITORY_MAP.md).

---

## Research boundaries

Several distinctions remain explicit:

- `B_i(phi)` is probabilistic threshold belief, not knowledge.
- Internal FDE negation is not generally meta-level absence of support.
- Primitive raw `Diamond` is not definitionally the same as `not K not`.
- The Liar and Gödel-inspired modules are not complete formalizations of semantic diagonalization or incompleteness.
- Conflict-Nerve Euler/signature results are formalized; general homology and persistence are not.
- Dynamic classification is complete for the current finite conditionalization and affine-path interfaces; arbitrary update-generated, continuous, and measure-theoretic paths remain open.
- Conditionalization requires the explicit `ConditionalizationAdmissible` safety contract; no update at zero local evidence mass is claimed.
- Exact necessity/minimality of every modal frame correspondence is not yet proved.
- Gate 8's split CPEL semantics remains model-induced. Gate 16 supplies a
  separate Boolean modal model class and Gate 18 a sound independent calculus,
  but no completeness theorem is yet supplied.
- The recovered ST/LP coincidence is antecedent-classical-restricted, not an unrestricted global collapse.
- Novelty claims for the combined structural and modal terminology require a systematic literature audit.

The project aims to distinguish **theorem, finite model, interpretation, and novelty claim** rather than collapse them into one layer.

---

## Current research direction

The active line has completed Gates 14--19. Recursive tolerant LEM plus
universal LP EFQ now exactly characterizes the compositional classical sector;
that sector is maximal relative to the declared recursive closure notion. A
separate Boolean probabilistic-epistemic semantics supplies truth
preservation/reflection and model-relative consequence equivalence on recovered
formulas. This remains narrower than unrestricted global collapse or
proof-system completeness. Gate 18 now supplies a sound independent classical
calculus, including a strong-probability boundary for belief monotonicity. Gate
19 characterizes uninterrupted recovery along finite conditionalization traces,
localizes the first loss, and exhibits later restoration.
Near-term priorities are:

1. determine whether finite traces admit useful bounds or normal forms for
   repeated recovery loss and return;
2. assess whether a later proof-theory gate should replace the single-premise
   calculus by finite contexts before attempting completeness;
3. connect matroid deletion/contraction to explicit epistemic transformations
   without identifying the two by stipulation;
4. eliminate the 20 convenience axioms listed in `docs/AXIOM_AUDIT.md` and
   complete the product-update prototype;
5. reconcile independent branches, especially the unmerged Alexandrov and
   persistent phase-nerve results;
6. perform the systematic literature and novelty audit required before
   publication-level priority claims.

The detailed backlog remains in `docs/RESEARCH_QUESTIONS.md`; the authoritative
structural overview is `docs/REPOSITORY_MAP.md`.

4-PEL is best read as a machine-checkable laboratory for the geometry, dynamics, modal structure, and information loss behind epistemic paradoxes.
