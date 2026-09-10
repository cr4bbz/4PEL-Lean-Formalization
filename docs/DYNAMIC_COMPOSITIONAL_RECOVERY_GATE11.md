# Gate 11: dynamic compositional recovery

## Research question

Which threshold, profile, and robustness conditions characterize preservation
of compositional classical recovery under admissible conditionalization?

Gate 11 connects the static recovery contract from Gate 10 with the existing
dynamic threshold and conditionalization theory. The initial formal slice is
implemented in `PEL4/DynamicCompositionalRecovery.lean`.

## Exact preservation boundary

Admissible conditionalization changes only the model's local probability
function. Atomic valuations, accessibility lists, and thresholds are preserved.
Consequently, the only new clauses that can fail in the Gate-10 recursive
contract are posterior threshold-completeness obligations at reachable `bel`
nodes.

`ModalFormula.PostUpdateBeliefCompleteAt` records exactly those obligations
along the same syntax and accessibility recursion as
`CompositionalRecoveryAt`. If `phi` is recovered before the update, Lean proves
the local equivalence:

```text
CompositionalRecoveryAt updated w phi
iff
PostUpdateBeliefCompleteAt before E hAdm w phi.
```

The corresponding global theorem is:

```text
CompositionalRecovery updated phi
iff
PostUpdateBeliefComplete before E hAdm phi.
```

This is an exact preservation criterion relative to prior recovery, not merely
a sufficient condition.

## Robust value and consequence preservation

The existing `ModalConditionalizationRobust` predicate guarantees equality of
the complete FDE value before and after an update. Combining it with Gate-10
recovery and prior probability integrity yields:

```text
prior compositional recovery
+ prior probability integrity
+ threshold-side robustness
-> posterior classical evaluation.
```

For a recovered, robust antecedent, the model-relative ST/LP consequence
collapse therefore remains valid after conditionalization. The consequent need
not itself be recovered or robust.

This value-level theorem is deliberately distinct from preservation of the
recursive recovery certificate. Robustness can preserve a compound value even
when it does not provide every internal posterior recovery obligation.

## Two-sided finite boundary

The existing three-world instability and restoration models now witness both
directions at the level of the Gate-10 recovery predicate.

Fracture:

```text
before: B p = T,T,T -> recovered
after:  B p = T,N,T -> not recovered
```

Restoration:

```text
before: B p = T,N,T -> not recovered
after:  B p = T,T,T -> recovered
```

Thus admissible conditionalization is neither monotone preservation nor
monotone destruction of compositional recovery. In both witnesses, atomic
valuation and accessibility stay fixed; the change is caused by posterior
threshold completeness at the belief layer.

## Theorem map

| Declaration | Role |
| --- | --- |
| `ModalFormula.PostUpdateBeliefCompleteAt` | local posterior obligation map |
| `compositionalRecoveryAt_conditionalize_iff_postUpdateBeliefCompleteAt` | exact local boundary |
| `ModalFormula.PostUpdateBeliefComplete` | global posterior obligation map |
| `compositionalRecovery_conditionalize_iff_postUpdateBeliefComplete` | exact global boundary |
| `evalModal_conditionalize_isClassical_of_recovery_and_robust` | robust classical-value preservation |
| `modalST_iff_LP_after_conditionalize_of_recovery_and_robust` | dynamic consequence transfer |
| `dynamic_instability_belP_recovered_before` | recovery before fracture |
| `dynamic_instability_belP_not_recovered_after` | recovery loss witness |
| `dynamic_restoration_belP_not_recovered_before` | non-recovery before restoration |
| `dynamic_restoration_belP_recovered_after` | recovery restoration witness |
| `conditionalization_recovery_is_not_monotone` | combined two-sided result |

## Audit and reproduction

```powershell
lake build
lake env lean PEL4/DynamicCompositionalRecoveryAxiomAudit.lean
```

The focused audit covers eleven principal Gate-11 declarations. On Lean 4.31
they depend only on the standard logical principles `propext`,
`Classical.choice`, and `Quot.sound`; no project-specific or native axiom is
introduced.

## Current nonclaims

The initial Gate-11 slice does not yet establish:

- preservation of probability integrity by the current minimal
  `ConditionalizationAdmissible` interface;
- equivalence between threshold-side robustness and recovery preservation;
- a purely numerical mass-straddling form of the recursive criterion;
- preservation under arbitrary action-model or product updates;
- unrestricted dynamic collapse of LP, ST, or classical consequence;
- minimal finite witnesses for every nested modal constructor.

## Next subgates

1. express posterior completeness through positive/negative threshold-wall
   crossings at every reachable belief node;
2. identify additional measure hypotheses under which conditionalization
   preserves `ModelProbabilityIntegrity`;
3. classify nested `know (bel phi)` and `poss (bel phi)` recovery transitions;
4. extend the analysis from probability-only conditionalization to the product
   update prototype;
5. lift the one-update theorem to finite update sequences.

