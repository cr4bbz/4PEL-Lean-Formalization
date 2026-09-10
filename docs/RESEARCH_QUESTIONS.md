# 4-PEL research question map

Active baseline: `research/recovered-classical-equivalence-gate17`.

Fresh verification on this baseline: Lean 4.31, 167 build jobs; 157 central
manuscript audit declarations; 24 MPFG audit declarations; six script tests;
54-page committed manuscript check. Repository structure and independent branch
boundaries are recorded in `docs/REPOSITORY_MAP.md`.

Status legend:

- **VERIFIED**: theorem or finite-model claim compiled on the active Lean 4.31 branch.
- **PARTIAL**: a substantial formal answer exists, but the general theorem or literature comparison is incomplete.
- **OPEN**: no satisfactory formal answer yet.
- **ACTIVE BUILD GATE**: code is on the research branch but must not be treated as compiler-verified until a fresh local build succeeds.
- **INTERPRETIVE**: a working philosophical diagnosis supported by formal results, not itself a machine-checked theorem.

For the consolidated modal picture, see `docs/MODAL_KNOWLEDGE_CLASSIFICATION.md`.

## A. Questions already answered formally

### A1. Does four-valued knowledge preserve complete information status?

**VERIFIED.** On homogeneous accessible profiles:

```text
T -> K(phi)=T
F -> K(phi)=F
B -> K(phi)=B
N -> K(phi)=N
```

Heterogeneous full-value profiles force `K(phi)=F`.

### A2. Is internal `not K phi` the same as meta-level lack of positive knowledge?

**VERIFIED: no.** Even reflexive, transitive, Euclidean frames do not collapse lack of positive knowledge, negative support for knowledge, and positive support for internal `not K phi`. A NoGap bridge is semantically independent of frame geometry.

### A3. What is the conjunction boundary for `K`?

**VERIFIED.** Positive introduction holds, positive elimination fails in general, and under `K+(phi and psi)` the exact extraction boundary is component stability. Strict conjunction decomposition survives.

### A4. Is raw possibility identical to `not K(not phi)`?

**VERIFIED: no.** They agree exactly when:

```text
Stable(phi) OR Diamond_raw(phi)=T.
```

Under instability, internal dualization can collapse to strict `T`.

### A5. What is the Church-Fitch boundary?

**VERIFIED conditionally.** Raw knowability, strict-truth phases, NoGap dependence, raw/dual separation, local Fitch recovery, and global Church-Fitch classification all compile.

### A6. What frame laws does evidence-stable knowledge satisfy?

**VERIFIED for the main boundaries.** Current classification:

```text
probability normalization -> seriality
reflexivity               -> strict factivity
transitivity              -> positive axiom 4 / value preservation on T,B
Euclideanness alone       -> insufficient for internal axiom 5
transitivity + Euclidean  -> full K-idempotence and K(not K phi)=not K phi
NoGap                     -> bridges meta-level ignorance to negative support
```

### A7. How do probabilistic belief `B` and evidence-stable knowledge `K` interact?

**VERIFIED, complete at the pointwise value level.** The central factorization is:

```text
K(phi) = if Stable(phi) then B(phi) else F.
```

Hence positive knowledge implies positive belief, positive belief upgrades to knowledge exactly under stability, all non-`F` K-values require stability, and instability is absorbed into strict `F`.

### A8. Does necessitation survive in 4-PEL?

**VERIFIED with an exact phase split.** Strict necessitation requires accessibility closure of the explicit validity domain. Positive necessitation additionally requires full-value stability. Under closure and positive validity:

```text
positive-valid(K phi)
iff
phi is full-value stable on every listed accessible range.
```

### A9. Does probability normalization constrain the frame?

**VERIFIED.** `mu(R)=1` together with `mu([])=0` implies every accessibility list is nonempty.

### A10. What happens to the Knower fixed point?

**VERIFIED.** The induced map is:

```text
T -> F
F -> T
B -> B
N -> N.
```

Working diagnosis: **epistemic fixed-point bifurcation**.

### A11. What is the Sorites threshold geometry?

**VERIFIED.** For scaled threshold `c > 50`, the gap interval is exactly `100-c < x < c`, with width `2c-100`. The same threshold slack controls glut overlap.

### A12. What fails in Surprise backward elimination?

**VERIFIED.** Each day can be predicted only in its own branch-relative updated context; these predictions do not transport back to the initial model. Working diagnosis: **context-collapse / prediction-transport failure**.

### A13. How much Preface conflict structure is invisible to marginals?

**VERIFIED.** Fixed first-order marginals leave freedom `2^n - n - 2` for `n >= 2`. Full co-conflict data reconstructs exact incidence by Möbius inversion. Support nerves with identical coarse data can have different Euler signatures.

### A14. Is conditionalization safe at zero evidence mass?

**VERIFIED.** The active API requires `ConditionalizationAdmissible m E` with positive local evidence mass and explicit normalization proofs. Liar, Surprise Examination, Surprise Backward Elimination, and the later dynamic modules compile through this safe interface.

### A15. Which modal formulas are invariant under probabilistic conditionalization?

**VERIFIED.** If `phi` contains no `bel` constructor, admissible conditionalization preserves its complete FDE value at every world. Consequently stability, outer `K`, and raw possibility are invariant for this fragment.

### A16. Can conditionalization create epistemic instability indirectly through belief?

**VERIFIED.** A finite three-world witness gives:

```text
before: B p = T,T,T
after:  B p = T,N,T
Stable(B p): true -> false
K(B p):       T   -> F.
```

Atomic `p` remains invariant in the same update. Working diagnosis: **Probabilistic Instability Injection** / **Belief-Mediated Stability Fracture**.

### A17. Can conditionalization restore epistemic stability?

**VERIFIED.** A second finite witness gives the converse transition:

```text
before: B p = T,N,T
after:  B p = T,T,T
Stable(B p): false -> true
K(B p):       F    -> T.
```

Together A16 and A17 show that conditionalization is neither monotone knowledge gain nor monotone knowledge loss.

### A18. Can evidence support be organized matroidally?

**VERIFIED for the channel-closure model.** The repository proves the closure
laws, FDE realization, channel-rank classification, circuit characterization,
circuit elimination, and deletion/contraction behavior for the chosen finite
evidence representation. This is not a claim that every empirical evidence
system is matroidal. See `docs/MATROID_EVIDENCE.md` and Gates 2–4.

### A19. When is a four-valued state structurally classical?

**VERIFIED.** Channel completeness excludes `N`, channel consistency excludes
`B`, and their conjunction characterizes exactly `{T,F}`. The recovered slice
is closed under the propositional FDE operations. Modal stability propagates a
recovered value but is not needed to create local classicality. See
`docs/CLASSICAL_RECOVERY_GATE5.md`.

### A20. Does atomic classicality lift to formulas?

**VERIFIED with an exact language boundary.** Atomic classicality propagates
through the propositional fragment. Belief and modal constructors require
additional profile and threshold recovery hypotheses; a finite witness shows
that atomic classicality alone does not force classical threshold belief. See
`docs/FORMULA_CLASSICAL_RECOVERY_GATE6.md`.

### A21. How does the Lockean threshold control recovery?

**VERIFIED.** For complementary classical support masses, at-most-half
thresholds rule out gaps but permit gluts, while supermajority thresholds rule
out gluts but permit gaps. Threshold regularity gives the exact classical-belief
boundary under probability integrity.

### A22. Does the split CPEL translation represent 4-PEL exactly?

**VERIFIED for the evaluator induced by 4-PEL models.** The two translated
Boolean coordinates recover the positive and negative FDE bits. On classical
values they lie on the anti-diagonal and collapse to one Boolean coordinate.
Gate 8 itself does not define an independent CPEL model class or complete
calculus. Gate 16 later adds a separate Boolean modal model class; an
independent proof calculus and completeness theorem remain open for Gate 18.
See `docs/CPEL_CLASSICAL_COLLAPSE_GATE8.md`.

### A23. Which classical laws return under recovery?

**VERIFIED.** Tolerant excluded middle is equivalent to gap-freedom, universal
value-level LP explosion to glut-freedom, and strict excluded middle to
classicality. Classicality is therefore equivalent to the conjunction of the
first two recovered laws.

### A24. Does recovery collapse ST and LP consequence?

**VERIFIED under an antecedent-classical restriction.** ST and LP coincide on
a fixed model when the antecedent is classical throughout that model, and the
global relations coincide after pointwise restriction to classical antecedent
evaluations. Unrestricted LP explosion still fails in an explicit finite
countermodel. See `docs/RECOVERY_CONSEQUENCE_TRANSFER_GATE9.md`.

### A25. Does classical recovery compose through the full modal language?

**VERIFIED for a semantic recursive recovery contract.** Atomic recovery,
propositional closure, accessible-profile recovery for knowledge and raw
possibility, and profile recovery plus threshold completeness for belief imply
classical `ModalFormula` evaluation on probability-integrity models. Globally
recovered modal antecedents make model-relative ST and LP consequence coincide.
Atomic classicality alone remains insufficient for belief, as witnessed by the
reused finite threshold-gap model. Necessity, update preservation, and the
largest syntactic recovered fragment remain open. See
`docs/COMPOSITIONAL_CLASSICAL_RECOVERY_GATE10.md`.

### A26. Is compositional recovery preserved by conditionalization?

**VERIFIED with an exact posterior-completeness boundary.** Relative to prior
recovery, posterior recovery is equivalent to threshold completeness at every
belief node reached by the recursive syntax/accessibility traversal. Prior
recovery plus threshold-side robustness preserves classical evaluation and the
model-relative ST/LP collapse after update. Finite three-world models prove
that admissible conditionalization can both destroy and restore the recovery
contract. The result is therefore non-monotone. See
`docs/DYNAMIC_COMPOSITIONAL_RECOVERY_GATE11.md`.

### A27. Which directed threshold crossings govern dynamic recovery?

**VERIFIED.** Symmetric threshold straddling decomposes into rise and fall, and
the four directed one-coordinate motions are exhaustive. From a prior classical
belief, gap creation is exactly `T -> N` by positive fall with negative support
remaining below, or `F -> N` by the dual pattern. Glut creation is exactly
`T -> B` or `F -> B` by a rise on the previously inactive side while the active
side remains above. A prior gap becomes complete exactly when at least one side
rises. Recursively, prior recovery plus probability integrity makes posterior
recovery equivalent to absence of these directed gap patterns at every
reachable belief node. See `docs/DIRECTIONAL_THRESHOLD_RECOVERY_GATE12.md`.

### A28. Does admissible conditionalization preserve finite probability integrity?

**VERIFIED, with a sharper minimality result.** If the prior model satisfies
`ModelProbabilityIntegrity`, the existing `ConditionalizationAdmissible`
contract preserves all six finite-probability fields in the posterior model.
No extra update axiom is required. Moreover, in this stronger prior class,
admissibility is equivalent to nonzero evidence mass alone: the total- and
empty-mass obligations are derivable quotient-measure laws.

Posterior integrity turns the Gate-12 no-directed-gap condition into an exact
equivalence with recursive semantic classicality throughout the updated model.
It also yields the posterior model-relative ST/LP coincidence without the
stronger Gate-11 value-invariance premise. Mere top-level classicality is not
claimed to characterize the recursive certificate. See
`docs/CONDITIONALIZATION_PROBABILITY_INTEGRITY_GATE13.md`.

## B. Questions with substantial but incomplete answers

### B1. Is the modal correspondence picture minimal?

**PARTIAL.** Sufficiency and important countermodels are verified, but exact weakest frame conditions are not classified for every law.

### B2. Is "paradox as structural-transport failure" a genuine common theory?

**PARTIAL / INTERPRETIVE.** Projection loss, non-commutation, stability failure, context transport failure, possibility-duality collapse, threshold phase change, fixed-point bifurcation, higher-order interaction loss, dynamic reachability, threshold-wall crossing, and crossing-order structure are represented formally. A sufficiently general theorem schema connecting these families remains open.

### B3. How novel are the combined results?

**OPEN LITERATURE QUESTION.** Individual ingredients have precedents in Belnap-Dunn logic, paraconsistent epistemic logic, nonstandard knowledge modalities, Fitch literature, dynamic epistemic logic, threshold belief, simplicial methods, and Möbius inversion. No strong novelty claim should precede a systematic comparison.

### B4. What is the epistemological reading of `K phi = B` and `K phi = N`?

**PARTIAL / INTERPRETIVE.** The formal distinctions are exact; the philosophical interpretation of glutty knowledge, gappy knowledge, internal ignorance, and meta-level lack of knowledge remains open.

## C. Dynamic and foundational research questions

### C1. What is the general dynamic K-change classification?

**VERIFIED.** `PEL4/ModalDynamicsPhaseClassification.lean` gives the complete stability table:

```text
stable -> stable     : K tracks B on both sides
stable -> unstable   : posterior K is forced to F
unstable -> stable   : prior K = F; posterior K tracks posterior B
unstable -> unstable : K = F on both sides
```

### C2. When do formulas containing `bel` nevertheless remain dynamically robust?

**VERIFIED at the threshold-semantic level.** `PEL4/ModalDynamicsRobustness.lean` proves that a belief value is invariant exactly when its positive and negative Lockean threshold bits are both invariant. `ModalConditionalizationRobust` propagates this protection compositionally through negation, conjunction, `K`, and raw possibility. A diagonal reachability witness proves the condition strictly extends `ModalProbabilityFree`.

Working diagnosis: **Threshold-Side Robustness**.

### C3. Which K/B values are dynamically reachable under fixed `R` and valuation?

**VERIFIED, complete.** `PEL4/ModalDynamicsReachability.lean` gives a fixed six-world model family such that every ordered pair

```text
source,target in {T,F,B,N}
```

is realized by safe conditionalization changing only probability:

```text
K(B p): source -> target.
```

Thus the categorical reachability graph contains all 16 directed transitions.

Working name: **Complete Dynamic Epistemic Reachability**.

### C4. Can dynamic updates create or remove K-gluts and K-gaps?

**VERIFIED: yes, in both directions.** The complete reachability theorem includes creation and removal of both `B` and `N`, including explicit witnesses such as `T -> B`, `B -> N`, and `N -> T`. No FDE status is dynamically terminal under admissible probabilistic conditionalization alone.

### C5. Algebraic characterization of stability

**OPEN.** Stability is currently semantic over accessible FDE profiles. Seek intrinsic algebraic, bilattice, or categorical descriptions and classify operators that preserve or reflect it.

### C6. Global independence/minimality of Church-Fitch assumptions

**OPEN.** Local independence witnesses exist, but the fully quantified global packages still deserve an explicit minimality table.

### C7. General theorem of structural transport

**OPEN, foundational.** Formalize transformations and observations generally enough to derive theorem families of the form:

```text
paradoxical inference requires preservation property P;
finite witness refutes P;
restricted hypotheses recover P.
```

### C8. Conflict topology beyond Euler signatures

**OPEN.** Add actual simplicial homology, Betti numbers, persistence, and realizability inside fixed-marginal fibers.

### C9. Continuous / measure-theoretic generalization

**OPEN.** Determine which finite rational results survive on countable or general probability spaces. The verified endpoint-straddling, affine threshold-hit, and affine crossing-order results now provide a concrete finite-dimensional path prototype before any general topology dependency is introduced.

### C10. Automated finite-model search

**OPEN, methodological.** A bounded generator over FDE valuations, relations, thresholds, and local measures could search for minimal witnesses and test conjectured correspondence laws.

### C11. Literature-grounded modal and dynamic comparison

**OPEN, publication-critical.** Compare primitive evidence-stable `K`, K/B factorization, exact positive necessitation boundary, probability-free invariance, threshold-side robustness, complete dynamic reachability, threshold-square geometry, threshold-straddling, affine threshold crossing, and crossing-order geometry with nonstandard Belnap-Dunn knowledge systems and four-valued dynamic epistemic logics.

### C12. What is the geometry of categorical dynamic displacement?

**VERIFIED.** `PEL4/ModalDynamicsGeometry.lean` treats

```text
N=(0,0), T=(1,0), F=(0,1), B=(1,1)
```

as the Boolean threshold square. `thresholdWallCount` is the Hamming-style number of positive/negative threshold coordinates that differ:

```text
0 walls -> same categorical state / robustness
1 wall  -> edge move in the threshold square
2 walls -> diagonal move (T<->F or N<->B).
```

The module proves symmetry, diameter two, zero-distance iff equality, and connects zero displacement to Threshold-Side Robustness. Complete Dynamic Epistemic Reachability realizes all three displacement classes.

Working name: **Threshold Square Geometry**.

### C13. What numerical event lies behind a categorical threshold-wall crossing?

**VERIFIED.** `PEL4/ModalDynamicsThresholdCrossing.lean` reconnects the Boolean square to the rational support masses. For one support coordinate:

```text
decide(c <= x) != decide(c <= y)
iff
one endpoint is on/above c and the other is below c.
```

At belief level the total wall count decomposes into positive and negative support wall counts. Lean verifies:

```text
0 walls -> neither support coordinate straddles threshold
1 wall  -> exactly one support coordinate straddles threshold
2 walls -> both support coordinates straddle threshold
belief value changes -> at least one support coordinate straddles threshold.
```

This closes the finite endpoint chain:

```text
support masses
  -> threshold sides
  -> threshold-wall count
  -> FDE belief status.
```

Working name: **Threshold-Straddle Geometry**.

### C14. Does endpoint straddling force a literal threshold hit along an explicit path?

**VERIFIED.** `PEL4/ModalDynamicsAffineCrossing.lean` defines the directed rational affine interpolation

```text
gamma(t) = x + t * (y - x)
```

and proves using only Lean Core rational arithmetic that threshold-straddling endpoints admit a rational crossing parameter:

```text
ThresholdStraddles c x y
->
exists t : Rat,
  0 <= t and t <= 1 and gamma(t) = c.
```

The result lifts to conditionalized belief support masses: every genuine categorical belief change forces a literal affine threshold hit on at least one support coordinate, and every two-wall transition forces hits on both coordinates.

This is a unit-interval crossing theorem for the chosen affine interpolation, not yet an abstract continuity theorem over arbitrary paths.

Working name: **Affine Threshold Crossing**.

### C15. Are the two affine wall crossings simultaneous or temporally ordered?

**VERIFIED.** `PEL4/ModalDynamicsCrossingOrder.lean` proves that a nonconstant affine support path hits a fixed threshold at at most one parameter. Hence each straddling coordinate has an intrinsic crossing time. Every two-wall belief transition admits a unique-time crossing pair with the exhaustive order:

```text
tp < tn   positive wall first
tp = tn   simultaneous
tn < tp   negative wall first.
```

The simultaneous case is equivalent to a common affine support parameter at which both coordinates equal the threshold, i.e. the two-dimensional path passes through `(c,c)`.

Working name: **Affine Crossing-Order Geometry**.

### C16. Which FDE phase appears between two nonsimultaneous affine wall crossings?

**VERIFIED.** `PEL4/ModalDynamicsIntermediatePhase.lean` chooses the rational midpoint between the two unique crossing times and proves the exact intermediate-state classification.

For positive-first order, the constructed midpoint has

```text
positive coordinate = target threshold side
negative coordinate = source threshold side.
```

For negative-first order the roles reverse. Thus every sequential diagonal transition passes through a vertex adjacent to both endpoints along the affine support interpolation. The verified table is:

```text
N -> B : positive first -> T ; negative first -> F
B -> N : positive first -> F ; negative first -> T
T -> F : positive first -> N ; negative first -> B
F -> T : positive first -> B ; negative first -> N.
```

The module deliberately classifies the constructed affine **support-mass path**. It does not yet claim that the midpoint corresponds to a full admissible intermediate probabilistic model.

Working name: **Affine Intermediate-Phase Geometry**.

## D. Research order after Gate 17

```text
COMPLETED Gate 14: recursive LEM/EFQ profile
COMPLETED Gate 15: maximality and necessity of the static recovery sector
COMPLETED Gate 16: independent Boolean probabilistic-epistemic semantics
COMPLETED Gate 17: recovered truth and consequence equivalence

NEXT DECISION Gate 18: choose proof-theoretic scope
  a. sound classical calculus
  b. soundness plus semantic completeness
  c. completeness plus decidability/canonical-model package

AFTER Gate 18: classify nested modal recovery across finite update sequences

LATER:
1. connect matroid minors to explicit epistemic transformations
2. eliminate convenience axioms and complete product update
3. integrate or explicitly archive independent research branches
4. perform the literature/novelty audit
5. revisit homology, persistence, and automated finite-model search
```

### D1. Classical-boundary research question (Gates 14--17)

**VERIFIED, with an explicit scope restriction.** The completed sequence answers:

> Is the compositional recovery sector the greatest subformula- and
> accessibility-recursive region in which tolerant LEM and universal LP EFQ
> hold at every relevant node, and does 4-PEL consequence there agree with an
> independently defined classical probabilistic-epistemic semantics?

The answer is yes relative to the declared recursive-fragment comparison class
and for formulas satisfying recovery. This is semantic conservativity, not yet
proof-system soundness or completeness. See the Gate 14--17 documents.

The methodological separation remains essential:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```
