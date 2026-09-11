# 4-PEL research question map

Active baseline: `research/recovery-causal-descent-gate23`.

Fresh verification on this baseline: Lean 4.31, 179 build jobs; 157 central
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
Gate 18 now supplies an independent sound calculus. Semantic completeness,
canonical models, and decidability remain open.
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

### A29. What happens to recovery along finite update sequences?

**VERIFIED for finite admissible conditionalization traces.** Because later
admissibility depends on earlier posterior models, Gate 19 introduces a
dependent trace type carrying strong probability integrity through every step.
For an initially recovered formula, recovery holds at every posterior state if
and only if no reachable belief node realizes a directed gap on any edge. If
this fails, the finite trace has an exact earliest directed-gap witness.

Recovery can nevertheless return later. A semantic return condition is proved
necessary and sufficient at one edge and lifted to arbitrary traces. A concrete
four-world sequence realizes `B(p): T -> N -> T`, so recovery of the final
state does not imply recovery throughout the run. See
`docs/FINITE_UPDATE_RECOVERY_GATE19.md`.

### A30. Is repeated finite evidence loss locally bounded?

**VERIFIED, with the global recovery-flip bridge still open.** Gate 20 compiles
a dependent conditionalization trace into the cumulative evidence restriction
at any fixed agent/world site. Lean proves

```text
final cumulative scope size + strict shrink count
<= initial accessibility-scope size.
```

Hence strict local shrinkage is bounded by both the initial scope length and
the trace length, and a three-world witness attains the cardinality bound. The
Gate-19 loss-and-return trace computes two strict local shrinkages. This does
not yet bound global recovery changes: recovery recursively observes several
formula-reachable belief sites. See
`docs/FINITE_UPDATE_SCOPE_BOUNDS_GATE20.md`.

### A31. Can every recovery change be localized finitely?

**VERIFIED for explicit finite roots; globally verified with world coverage.**
Gate 21 compiles an exact finite list of the atomic and belief-result
classicality observations inspected by a formula's recursive recovery
certificate. Under probability integrity, recovery on the finite roots holds
if and only if every compiled observation is classical.

Conditionalization preserves the observation map itself because it leaves
accessibility and syntax fixed. Lean proves the stuttering theorem and its
contrapositive:

```text
all compiled statuses stutter -> recovery stutters;
recovery changes -> some compiled belief-result status changes.
```

The globally quantified version requires an explicit proof that the finite
root list covers the ambient world type. The Gate-19 instance compiles twenty
observation positions and exhibits `B(p)` at world `a` as a concrete witness
to the first recovery loss. See
`docs/FINITE_REACHABLE_RECOVERY_GATE21.md`.

### A32. Does every changed belief observation spend local scope budget?

**VERIFIED AS AN EXACT DICHOTOMY; THE UNQUALIFIED CLAIM IS TOO STRONG.** Gate
22 proves that posterior measures are concentrated on the cumulative Gate-20
scope after every finite update prefix. Consequently,

```text
no strict local scope loss + no accessible body-value change
-> complete four-valued belief result stutters.
```

Every changed belief classicality status therefore implies either strict
cumulative-scope shrinkage at that agent/world coordinate or a changed body
value at an accessible world. Combining this with Gate 21 gives the same
dichotomy for a compiled witness to every finite-root recovery change.

The body-change alternative shows why the anticipated pointwise
change-to-budget injection is not yet justified: change may be inherited from
deeper in the modal evaluation tree. See
`docs/RECOVERY_SCOPE_STUTTERING_GATE22.md`.

### A33. Does inherited modal change reach a strict scope loss?

**VERIFIED.** Gate 23 follows every changed modal value through the finite
syntax and accessibility tree. Negation and conjunction descend structurally;
knowledge and possibility descend through an accessible changed body value;
belief either shrinks locally or uses Gate 22 to descend into its body. Atomic
values cannot change under conditionalization.

Lean therefore proves:

```text
recovery changes on finite roots
-> some belief observation in the original Gate-21 compiler
   has strict cumulative-scope shrinkage.
```

The result lifts to global recovery under `WorldListCovers` and specializes to
the next edge after any dependent finite update prefix. It establishes causal
localization, not yet an injective count of repeated changes. See
`docs/RECOVERY_CAUSAL_DESCENT_GATE23.md`.

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

## D. Research order after Gate 23

```text
COMPLETED Gate 14: recursive LEM/EFQ profile
COMPLETED Gate 15: maximality and necessity of the static recovery sector
COMPLETED Gate 16: independent Boolean probabilistic-epistemic semantics
COMPLETED Gate 17: recovered truth and consequence equivalence
COMPLETED Gate 18: independent classical calculus and soundness
COMPLETED Gate 19: finite update traces, first loss, and recovery return
COMPLETED Gate 20: sharp local cumulative evidence-scope bounds
COMPLETED Gate 21: exact finite recovery-observation maps and stuttering
COMPLETED Gate 22: posterior concentration and local causal dichotomy
COMPLETED Gate 23: recursive descent to strict reachable scope loss

NEXT DECISION:
1. define trace-level counting of recovery-changing edges
2. aggregate Gate-20 budgets over finite Gate-21 belief positions
3. derive a finite global recovery-flip bound under world coverage
4. optionally sharpen it by deduplicating agent/world coordinates
5. extend the trace analysis to product updates
6. return to the deferred finite-context proof theory

DEFERRED PROOF THEORY:
1. assess finite-context versus single-premise presentation
2. specify the intended threshold-belief axiomatics
3. only then attempt semantic completeness or decidability

LATER:
1. connect matroid minors to explicit epistemic transformations
2. eliminate convenience axioms and complete product update
3. integrate or explicitly archive independent research branches
4. perform the literature/novelty audit
5. revisit homology, persistence, and automated finite-model search
```

### D1. Classical-boundary research question (Gates 14--18)

**VERIFIED, with an explicit scope restriction.** The completed sequence answers:

> Is the compositional recovery sector the greatest subformula- and
> accessibility-recursive region in which tolerant LEM and universal LP EFQ
> hold at every relevant node, and does 4-PEL consequence there agree with an
> independently defined classical probabilistic-epistemic semantics?

The answer is yes relative to the declared recursive-fragment comparison class
and for formulas satisfying recovery. Gate 18 additionally proves soundness for
an independent classical calculus on this strong semantic sector; completeness
remains open. See the Gate 14--18 documents.

The methodological separation remains essential:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```

### D2. Repeated-change bound (Gate 20)

**LOCALLY VERIFIED; GLOBAL BRIDGE OPEN.** For every fixed agent/world belief
site in a dependent finite conditionalization trace, Lean proves

```text
final cumulative scope size + strict cumulative shrink count
<= initial accessibility-scope size.
```

The bound is sharp. The Gate-19 `T -> N -> T` witness exhibits two strict
local scope losses alongside its two recovery changes. This coincidence is not
promoted to a general theorem: compositional recovery ranges recursively over
multiple belief sites. A global flip bound now requires a finite compiler for
the sites reachable from a formula and a theorem that recovery stutters when
all compiled local data stutter.

### D3. Finite recovery localization (Gate 21)

**VERIFIED; NUMERICAL AGGREGATION OPEN.** The finite reachable-site compiler
and recovery-stuttering bridge requested by Gate 20 now exist. For finite roots,
every recovery change has a changed belief-result observation in an exact
finite list; atomic observations provably stutter. With `WorldListCovers`, this localizes changes of the original global
recovery predicate as well.

The remaining step is quantitative rather than merely logical: prove that a
changed compiled belief observation consumes a strict Gate-20 evidence/support
resource, then prevent the same consumed resource from being counted again.

### D4. Cumulative-scope stuttering (Gate 22)

**VERIFIED; CAUSAL DESCENT RESOLVED BY GATE 23.** The cumulative Gate-20 scope now
has a proved probabilistic meaning: after every update prefix, the posterior
measure is concentrated on its final scope. An update that removes no further
scope world preserves all local event masses. If the accessible interpretation
of a belief body also stutters, the complete FDE belief value stutters.

The contrapositive refines every Gate-21 recovery witness to:

```text
strict scope shrinkage at this belief coordinate
or
an inherited body-value change at an accessible world.
```

Thus the earlier proposed direct injection from every changed compiled belief
observation to its own local budget is too coarse. Gate 23 now proves the
terminating recursive causal search through the finite modal evaluation tree:
because atomic valuations do not change, its endpoint is a reachable belief
coordinate whose cumulative scope strictly shrinks. Coordinate deduplication
and budget summation remain open.

### D5. Recursive causal localization (Gate 23)

**VERIFIED; DUPLICATE-FREE ACCOUNTING OPEN.** Every changed modal value under
one admissible conditionalization now yields a belief observation in its exact
Gate-21 compiler whose current cumulative scope shrinks strictly. Compiler
closure lifts a descendant found below a changed observation back into the
original finite-root map. Gate-21 recovery localization then supplies the
recovery theorem, and Gate-22 concentration supplies its trace-indexed form.

This closes the qualitative causal chain:

```text
recovery change
-> changed compiled observation
-> finite recursive value descent
-> strict scope loss at a reachable belief observation.
```

It does not yet close the quantitative chain. Repeated syntactic positions may
refer to the same agent/world coordinate, and one strict loss may change many
observations on a single edge. Gate 24 can nevertheless sum over all finite
belief positions: duplicates only make this first upper bound larger. A later
coordinate quotient can sharpen the bound without being a prerequisite for
finiteness.
