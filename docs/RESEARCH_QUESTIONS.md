# 4-PEL research question map

Status legend:

- **VERIFIED**: theorem or finite-model claim compiled on the active Lean 4.31 branch.
- **PARTIAL**: a substantial formal answer exists, but the general theorem or literature comparison is incomplete.
- **OPEN**: no satisfactory formal answer yet.
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

**VERIFIED: no.** The repository separates:

```text
(K phi).pos = false
(K phi).neg = true
(not K phi).pos = true
```

Even reflexive, transitive, Euclidean frames do not collapse these notions. A NoGap bridge is semantically independent of frame geometry.

### A3. What is the conjunction boundary for `K`?

**VERIFIED.** Positive introduction holds:

```text
K+ phi and K+ psi -> K+(phi and psi)
```

but positive elimination fails. Under `K+(phi and psi)`:

```text
K+ phi iff Stable(phi)
K+ psi iff Stable(psi).
```

Strict conjunction decomposition survives.

### A4. Is raw possibility identical to `not K(not phi)`?

**VERIFIED: no.** They agree exactly when:

```text
Stable(phi) OR Diamond_raw(phi)=T.
```

Under instability, internal dualization can collapse to strict `T`.

### A5. What is the Church-Fitch boundary?

**VERIFIED conditionally.** Raw knowability, strict-truth phases, NoGap dependence, raw/dual separation, local Fitch recovery, and global Church-Fitch classification all compile. Positive raw knowability yields omniscience only with the required information-status and recovery assumptions.

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

Hence:

```text
K+ phi -> B+ phi
B+ phi -> (K+ phi iff Stable(phi))
K phi = v, v != F iff Stable(phi) and B phi = v
K phi = F iff Unstable(phi) or B phi = F.
```

Working interpretation: **knowledge is stability-filtered belief**.

### A8. Does necessitation survive in 4-PEL?

**VERIFIED with an exact phase split.** Strict necessitation requires accessibility closure of the explicit validity domain:

```text
strict-valid(phi) + closure -> strict-valid(K phi).
```

Without closure, a hidden accessible counterworld refutes the rule.

For positive validity, closure alone is insufficient. Under closure and positive validity:

```text
positive-valid(K phi)
iff
phi is full-value stable on every listed accessible range.
```

At schema level:

```text
positive necessitation
iff
every positively valid formula is accessibility-stable.
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

**VERIFIED.** For scaled threshold `c > 50`, the gap interval is exactly:

```text
100-c < x < c
```

with width `2c-100`. The same threshold slack controls glut overlap.

### A12. What fails in Surprise backward elimination?

**VERIFIED.** Each day can be predicted only in its own branch-relative updated context; these predictions do not transport back to the initial model. Working diagnosis: **context-collapse / prediction-transport failure**.

### A13. How much Preface conflict structure is invisible to marginals?

**VERIFIED.** Fixed first-order marginals leave freedom:

```text
2^n - n - 2
```

for `n >= 2`. Full co-conflict data reconstructs exact incidence by Möbius inversion. Support nerves with identical coarse data can have different Euler signatures.

### A14. Is the old conditionalization operator semantically safe at zero evidence mass?

**VERIFIED: the old prototype was not.** Raw conditionalization returned `0` for zero mass while normalization had been postulated unconditionally.

The active API now requires:

```text
ConditionalizationAdmissible m E
```

with positive local evidence mass and explicit normalization proofs. Liar, Surprise Examination, and Surprise Backward Elimination compile through this safe interface.

### A15. Which modal formulas are invariant under probabilistic conditionalization?

**VERIFIED.** If `phi` contains no `bel` constructor, then admissible conditionalization preserves its complete FDE value at every world:

```text
ModalProbabilityFree(phi)
-> value_after(phi)=value_before(phi).
```

Consequently stability, outer `K`, and raw possibility are invariant for this fragment.

### A16. Can conditionalization create epistemic instability indirectly through belief?

**VERIFIED.** A finite three-world witness gives:

```text
before: B p = T,T,T
 after: B p = T,N,T
```

under admissible evidence update. Therefore:

```text
Stable(B p): true -> false
K(B p):       T   -> F.
```

Atomic `p` remains invariant in the same update. Working diagnosis: **Probabilistic Instability Injection** / **Belief-Mediated Stability Fracture**.

## B. Questions with substantial but incomplete answers

### B1. Is the modal correspondence picture minimal?

**PARTIAL.** Sufficiency and important countermodels are verified, but exact weakest frame conditions are not classified for every law. Open examples include minimal conditions for full K-idempotence and internal axiom 5.

### B2. Is "paradox as structural-transport failure" a genuine common theory?

**PARTIAL / INTERPRETIVE.** Projection loss, non-commutation, stability failure, context transport failure, possibility-duality collapse, threshold phase change, fixed-point bifurcation, and higher-order interaction loss are all represented formally in different modules. A sufficiently general theorem schema connecting these families remains open.

### B3. How novel are the combined results?

**OPEN LITERATURE QUESTION.** Individual ingredients have precedents in Belnap-Dunn logic, paraconsistent epistemic logic, nonstandard knowledge modalities, Fitch literature, dynamic epistemic logic, threshold belief, simplicial methods, and Möbius inversion. No strong novelty claim should precede a systematic comparison.

### B4. What is the epistemological reading of `K phi = B` and `K phi = N`?

**PARTIAL / INTERPRETIVE.** The formal distinctions are exact; the philosophical interpretation of glutty knowledge, gappy knowledge, internal ignorance, and meta-level lack of knowledge remains open.

## C. High-priority open research questions

### C1. Can conditionalization also restore epistemic stability?

**OPEN, active build gate.** `PEL4/ModalDynamicsBeliefRestoration.lean` tests:

```text
before: B p = T,N,T -> unstable -> K(B p)=F
after:  B p = T,T,T -> stable   -> K(B p)=T.
```

If verified, probabilistic conditionalization will be shown to move stability in both directions rather than being monotone knowledge gain or loss.

### C2. What is the general dynamic K-change classification?

**OPEN, high priority.** Once fracture and restoration are established, classify dynamic change by the pair:

```text
belief-value change
stability change.
```

The K/B factorization suggests a phase table in which all knowledge changes arise from one or both of these channels.

### C3. When do formulas containing `bel` nevertheless remain dynamically stable?

**OPEN.** `ModalProbabilityFree` is a strong syntactic sufficient condition, not an exact semantic characterization. Seek weaker conditions such as posterior-uniformity of relevant belief subformulas across accessible worlds.

### C4. Which K/B values are dynamically reachable under fixed `R` and valuation?

**OPEN.** Current witnesses show at least `K(Bp): T -> F` and the active restoration gate tests `F -> T`. A complete reachability graph over `T,F,B,N` would expose the geometry of dynamic epistemic phases.

### C5. Can dynamic updates create or remove K-gluts and K-gaps?

**OPEN.** The current witnesses focus on strict `T/F`. Construct and classify updates involving `B` and `N` at the knowledge level.

### C6. Algebraic characterization of stability

**OPEN.** Stability is currently semantic over accessible FDE profiles. Seek intrinsic algebraic, bilattice, or categorical descriptions and classify operators that preserve or reflect it.

### C7. Global independence/minimality of Church-Fitch assumptions

**OPEN.** Local independence witnesses exist, but the fully quantified global packages still deserve an explicit minimality table.

### C8. General theorem of structural transport

**OPEN, foundational.** Formalize transformations and observations generally enough to derive theorem families of the form:

```text
paradoxical inference requires preservation property P;
finite witness refutes P;
restricted hypotheses recover P.
```

### C9. Conflict topology beyond Euler signatures

**OPEN.** Add actual simplicial homology, Betti numbers, persistence, and realizability inside fixed-marginal fibers.

### C10. Continuous / measure-theoretic generalization

**OPEN.** Determine which finite rational results survive on countable or general probability spaces.

### C11. Automated finite-model search

**OPEN, methodological.** A bounded generator over FDE valuations, relations, thresholds, and local measures could search for minimal witnesses and test conjectured correspondence laws.

### C12. Literature-grounded modal and dynamic comparison

**OPEN, publication-critical.** Compare primitive evidence-stable `K`, the K/B factorization, exact positive necessitation boundary, and dynamic stability fracture/restoration pattern with nonstandard Belnap-Dunn knowledge systems and four-valued dynamic epistemic logics.

## D. Suggested research order

```text
1. verify belief-mediated stability restoration
2. derive a general dynamic K-change phase classification
3. sharpen semantic preservation conditions beyond ModalProbabilityFree
4. classify dynamic reachability of T/F/B/N
5. revisit frame-law minimality
6. perform literature/novelty audit
7. strengthen the general structural-transport abstraction
8. deepen conflict topology and persistence
```

The methodological separation remains essential:

```text
machine-checked theorem
finite executable witness
structural/philosophical interpretation
literature/novelty claim.
```
