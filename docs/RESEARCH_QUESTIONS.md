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

**VERIFIED: the old prototype was not.** The active API now requires:

```text
ConditionalizationAdmissible m E
```

with positive local evidence mass and explicit normalization proofs. Liar, Surprise Examination, and Surprise Backward Elimination compile through this safe interface.

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

The restoration update conditions directly on positive `p`-evidence. Accessibility and atomic valuation remain fixed.

Together A16 and A17 show that conditionalization is neither monotone knowledge gain nor monotone knowledge loss. Working interpretation: **epistemic stability-phase transition**.

## B. Questions with substantial but incomplete answers

### B1. Is the modal correspondence picture minimal?

**PARTIAL.** Sufficiency and important countermodels are verified, but exact weakest frame conditions are not classified for every law.

### B2. Is "paradox as structural-transport failure" a genuine common theory?

**PARTIAL / INTERPRETIVE.** Projection loss, non-commutation, stability failure, context transport failure, possibility-duality collapse, threshold phase change, fixed-point bifurcation, and higher-order interaction loss are represented formally. A sufficiently general theorem schema connecting these families remains open.

### B3. How novel are the combined results?

**OPEN LITERATURE QUESTION.** Individual ingredients have precedents in Belnap-Dunn logic, paraconsistent epistemic logic, nonstandard knowledge modalities, Fitch literature, dynamic epistemic logic, threshold belief, simplicial methods, and Möbius inversion. No strong novelty claim should precede a systematic comparison.

### B4. What is the epistemological reading of `K phi = B` and `K phi = N`?

**PARTIAL / INTERPRETIVE.** The formal distinctions are exact; the philosophical interpretation of glutty knowledge, gappy knowledge, internal ignorance, and meta-level lack of knowledge remains open.

## C. Dynamic and foundational research questions

### C1. What is the general dynamic K-change classification?

**VERIFIED.** `PEL4/ModalDynamicsPhaseClassification.lean` lifts the pointwise K/B factorization into the complete two-state stability table:

```text
stable -> stable     : K tracks B on both sides
stable -> unstable   : posterior K is forced to F
unstable -> stable   : prior K = F; posterior K tracks posterior B
unstable -> unstable : K = F on both sides
```

The verified fracture and restoration models realize both off-diagonal phases.

### C2. When do formulas containing `bel` nevertheless remain dynamically robust?

**VERIFIED at the threshold-semantic level.** `PEL4/ModalDynamicsRobustness.lean` proves that a belief value is invariant exactly when its positive and negative Lockean threshold bits are both invariant. `ModalConditionalizationRobust` propagates this protection compositionally through negation, conjunction, `K`, and raw possibility. A diagonal reachability witness proves the condition strictly extends `ModalProbabilityFree`: a formula containing `bel` can be robust under a nontrivial probability update.

Working diagnosis: **Threshold-Side Robustness**.

### C3. Which K/B values are dynamically reachable under fixed `R` and valuation?

**VERIFIED, complete.** `PEL4/ModalDynamicsReachability.lean` gives a fixed six-world model family such that for every ordered pair

```text
source,target in {T,F,B,N}
```

safe conditionalization changes only the probability measure and realizes

```text
K(B p): source -> target.
```

Thus the categorical reachability graph has all 16 directed transitions.

Working name: **Complete Dynamic Epistemic Reachability**.

### C4. Can dynamic updates create or remove K-gluts and K-gaps?

**VERIFIED: yes, in both directions.** The complete reachability theorem includes creation and removal of both `B` and `N`, including explicit witnesses such as

```text
T -> B
B -> N
N -> T.
```

No FDE status is dynamically terminal under the semantics of admissible probabilistic conditionalization alone.

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

**OPEN.** Determine which finite rational results survive on countable or general probability spaces.

### C10. Automated finite-model search

**OPEN, methodological.** A bounded generator over FDE valuations, relations, thresholds, and local measures could search for minimal witnesses and test conjectured correspondence laws.

### C11. Literature-grounded modal and dynamic comparison

**OPEN, publication-critical.** Compare primitive evidence-stable `K`, K/B factorization, exact positive necessitation boundary, probability-free invariance, threshold-side robustness, complete dynamic reachability, and bidirectional stability transitions with nonstandard Belnap-Dunn knowledge systems and four-valued dynamic epistemic logics.

### C12. What is the geometry of categorical dynamic displacement?

**ACTIVE BUILD GATE.** `PEL4/ModalDynamicsGeometry.lean` treats

```text
N=(0,0), T=(1,0), F=(0,1), B=(1,1)
```

as the Boolean threshold square and defines `thresholdWallCount` as the number of positive/negative threshold coordinates that differ. The target classification is:

```text
0 walls -> same categorical state / robustness
1 wall  -> edge move in the threshold square
2 walls -> diagonal move (T<->F or N<->B)
```

The module also connects zero displacement to Threshold-Side Robustness and the complete reachability family to arbitrary 0/1/2 displacement. Do not mark this gate verified until a fresh local `lake build` succeeds.

## D. Suggested research order

```text
1. compile Threshold Square Geometry
2. ask whether continuous probability paths force literal threshold-wall crossings
3. seek algebraic/bilattice characterization of stability
4. revisit frame-law and Church-Fitch minimality
5. strengthen the general structural-transport abstraction
6. perform literature/novelty audit
7. deepen conflict topology to homology and persistence
8. investigate automated finite-model search
```

The methodological separation remains essential:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```
