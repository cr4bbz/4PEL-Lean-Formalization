# 4-PEL research question map

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

## B. Questions with substantial but incomplete answers

### B1. Is the modal correspondence picture minimal?

**PARTIAL.** Sufficiency and important countermodels are verified, but exact weakest frame conditions are not classified for every law.

### B2. Is "paradox as structural-transport failure" a genuine common theory?

**PARTIAL / INTERPRETIVE.** Projection loss, non-commutation, stability failure, context transport failure, possibility-duality collapse, threshold phase change, fixed-point bifurcation, higher-order interaction loss, dynamic reachability, and threshold-wall crossing are represented formally. A sufficiently general theorem schema connecting these families remains open.

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

**OPEN.** Determine which finite rational results survive on countable or general probability spaces. The verified threshold-straddling endpoint theorem and the active affine crossing gate provide a natural bridge toward a continuous path layer.

### C10. Automated finite-model search

**OPEN, methodological.** A bounded generator over FDE valuations, relations, thresholds, and local measures could search for minimal witnesses and test conjectured correspondence laws.

### C11. Literature-grounded modal and dynamic comparison

**OPEN, publication-critical.** Compare primitive evidence-stable `K`, K/B factorization, exact positive necessitation boundary, probability-free invariance, threshold-side robustness, complete dynamic reachability, threshold-square geometry, threshold-straddling, and affine threshold crossing with nonstandard Belnap-Dunn knowledge systems and four-valued dynamic epistemic logics.

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

**ACTIVE BUILD GATE.** `PEL4/ModalDynamicsAffineCrossing.lean` defines the directed rational affine interpolation

```text
gamma(t) = x + t * (y - x)
```

and attempts to prove, using only Lean Core rational arithmetic, that threshold-straddling endpoints admit an explicit rational crossing parameter:

```text
ThresholdStraddles c x y
->
exists t : Rat,
  0 <= t and t <= 1 and gamma(t) = c.
```

The gate then lifts the result to conditionalized belief support masses. A genuine belief-status change should force an affine threshold hit on at least one support coordinate; a two-wall transition should force hits on both coordinates, possibly at different parameters.

This would be a unit-interval crossing theorem for the chosen affine interpolation, not yet an abstract continuity or intermediate-value theorem over arbitrary paths.

Working name: **Affine Threshold Crossing**.

## D. Suggested research order

```text
1. compile Affine Threshold Crossing
2. if successful, characterize simultaneous vs sequential two-coordinate crossings in the support plane
3. decide whether general path continuity now justifies a topology dependency
4. seek algebraic/bilattice characterization of stability
5. revisit frame-law and Church-Fitch minimality
6. strengthen the general structural-transport abstraction
7. perform literature/novelty audit
8. deepen conflict topology to homology and persistence
9. investigate automated finite-model search
```

The methodological separation remains essential:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```
