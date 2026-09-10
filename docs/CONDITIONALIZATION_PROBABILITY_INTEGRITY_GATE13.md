# Gate 13: probability integrity under conditionalization

## Research question

Under which strengthened finite conditionalization contract is
`ModelProbabilityIntegrity` preserved, so that the Gate-12 directional recovery
criterion yields an exact posterior classicality theorem?

Gate 13 is implemented in
`PEL4/ConditionalizationProbabilityIntegrity.lean`.

## Main finding: no new update axiom is needed

The expected task was to strengthen `ConditionalizationAdmissible` with fields
for nonnegativity, extensionality, monotonicity, and finite additivity. Lean shows
that this would be redundant.

If the prior model satisfies `ModelProbabilityIntegrity`, then the positive
extension of the evidence formula is automatically:

- a duplicate-free finite event;
- a subset of the local accessible support;
- assigned nonnegative mass.

The existing admissibility condition says that this mass is nonzero. Hence it is
strictly positive, and the usual quotient construction inherits every required
finite-probability law.

Lean proves:

```text
ModelProbabilityIntegrity m
+ ConditionalizationAdmissible m E
-> ModelProbabilityIntegrity (conditionalize m E hAdm).
```

The theorem is
`conditionalize_preserves_probabilityIntegrity`.

## A sharper minimality result

On an integrity-certified prior, the existing three-field admissibility
structure is equivalent to its positive-mass field alone:

```text
ConditionalizationAdmissible m E
iff
forall i w, conditionalizationEvidenceMass m i w E != 0.
```

The total-mass and empty-mass fields are therefore derivable properties of the
quotient update, not independent assumptions in this stronger model class. This
is formalized by
`conditionalizationAdmissible_iff_positiveMass_of_probabilityIntegrity`.

This is the principal methodological result of Gate 13: the required
strengthening belongs to the **prior model contract**, not to the update
constructor.

## Why the quotient measure remains integral

For local support `R`, evidence event `E+`, and event `S`, the update is

```text
mu_E(S) = mu(S intersect E+) / mu(E+).
```

The formal proof derives:

1. filtered and intersected lists remain duplicate-free;
2. all numerators stay inside `R`;
3. extensional events have extensionally equal intersections;
4. inclusion is preserved by intersection;
5. disjointness is preserved by intersection;
6. intersection distributes over list append;
7. division by the positive constant `mu(E+)` preserves nonnegativity and
   monotonicity;
8. distributivity yields finite additivity;
9. `R intersect E+` is extensionally `E+`, yielding total mass one;
10. the empty intersection has mass zero.

`conditionalizeStrong` packages the result as a new `StrongProbabilityModel`.

## Exact posterior compositional classicality

Gate 13 distinguishes a classical top-level value from recursive classicality
at every node relevant to the recovery traversal. The latter is named
`ModalFormula.CompositionallyClassical`.

Under probability integrity, Lean proves the exact static equivalence:

```text
CompositionalRecovery m phi
iff
CompositionallyClassical m phi.
```

The belief case contains the important division of labor:

- threshold completeness excludes the gap `N`;
- probability integrity plus the built-in supermajority threshold excludes the
  glut `B` on a classical accessible profile.

Combining this equivalence, posterior integrity, and Gate 12 gives the main
Gate-13 theorem:

```text
CompositionallyClassical (conditionalize m E hAdm) phi
iff
NoDirectionalGap m E hAdm phi,
```

assuming prior probability integrity and prior compositional recovery.

Thus the directed condition is now both a recovery-certificate criterion and an
exact recursive semantic classicality criterion. As an observable corollary,
the updated formula evaluates to `T` or `F` at every world whenever the directed
gap pattern is absent.

## Consequence-level payoff

Gate 11 obtained the posterior ST/LP coincidence from full threshold-side
robustness, which preserves the complete value. Gate 13 needs less: prior
recovery plus absence of directed gaps suffices. The update may change a
classical value from `T` to `F` or conversely; value invariance is unnecessary.

This is formalized by
`modalST_iff_LP_after_conditionalize_of_noDirectionalGap`.

## Theorem map

| Declaration | Role |
| --- | --- |
| `filterWorlds_nodup` | filtering preserves event well-formedness |
| `intersectWorlds_*` | subset, extensionality, monotonicity, disjointness, and append lemmas |
| `conditionalizationEvidenceEvent_nodup` | the evidence event is duplicate-free |
| `conditionalizationEvidenceEvent_subset` | the evidence event lies inside accessibility |
| `conditionalizationAdmissible_iff_positiveMass_of_probabilityIntegrity` | exact minimal admissibility boundary |
| `conditionalizationEvidenceMass_pos` | nonzero evidence mass becomes strictly positive |
| `conditionalize_preserves_probabilityIntegrity` | quotient update preserves all finite-probability laws |
| `conditionalizeStrong` | strong-model update constructor |
| `compositionalRecoveryAt_iff_compositionallyClassicalAt` | local exact semantic reading of the certificate |
| `compositionalRecovery_iff_compositionallyClassical` | global exact semantic reading |
| `compositionalClassical_conditionalize_iff_noDirectionalGap` | Gate-13 main theorem |
| `evalModal_conditionalize_isClassical_of_noDirectionalGap` | top-level classical-value corollary |
| `modalST_iff_LP_after_conditionalize_of_noDirectionalGap` | posterior consequence collapse |

## Verification

```powershell
lake build
lake env lean PEL4/ConditionalizationProbabilityIntegrityAxiomAudit.lean
```

The focused audit contains twenty-one selected declarations. They use only
Lean's standard logical principles (`propext`, `Classical.choice`, and
`Quot.sound`) or subsets thereof. Gate 13 introduces no project-specific axiom
and uses no native-decision axiom.

## Current nonclaims

Gate 13 does not establish:

- that every legacy model satisfies `ModelProbabilityIntegrity`;
- that zero-mass evidence is admissible;
- that every formula avoids a directed gap;
- that mere top-level classicality is equivalent to the recursive recovery
  certificate—classicality can occur accidentally above a nonclassical
  subformula;
- preservation for the separate product-update prototype;
- an update-generated continuous path between prior and posterior models.

## Subsequent ordering decision

Gate 13 originally recommended finite update sequences next. That recommendation
was superseded by the classical-boundary sequence completed as Gates 14--18.
Gate 19 now implements finite update sequences. Gate 13 supplies their central
induction invariant: every intermediate positive-mass update remains
probability-integrity-certified.
