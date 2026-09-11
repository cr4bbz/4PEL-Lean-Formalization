# Gate 24: finite recovery-flip budget

## Research question

Can the number of recovery-changing edges in an arbitrary finite admissible
conditionalization trace be bounded by the finite Gate-20 resources attached
to the belief positions in the exact Gate-21 observation compiler?

## Answer

Yes. Gate 24 proves the stronger invariant

```text
recovery changes already incurred
+ final remaining position-wise scope potential
<= initial position-wise scope potential.
```

Consequently,

```text
number of recovery-changing edges
<= sum of initial accessibility-scope lengths
   over all compiled belief observations.
```

The right-hand side depends on the initial model, roots, and formula, but not
on the length of the trace. The trace may therefore contain arbitrarily many
admissible update edges while recovery can change only finitely often under
this fixed finite compiler budget.

## Proof architecture

The formal argument combines the previous four gates.

1. Gate 21 gives the exact finite recovery-observation compiler and proves
   that it is invariant under conditionalization.
2. Gate 22 proves posterior concentration on every cumulative evidence scope.
3. Gate 23 turns each recovery-status change into at least one strict scope
   shrinkage at a compiled belief observation.
4. Gate 20 ensures that a strict shrinkage consumes at least one unit of the
   corresponding finite scope length.

Gate 24 sums the one-position inequalities over the compiler and then performs
induction over the dependent finite trace. The proof retains the final unused
potential instead of discarding it.

## Computed status and global reading

`recoveryStatusOnBool` is an executable Boolean status for recovery on explicit
finite roots. Lean proves that it is true exactly when
`CompositionalRecoveryOn` holds. If `WorldListCovers roots`, it is also exactly
the repository's globally quantified `CompositionalRecovery` predicate.

Thus the numerical count has a global recovery reading only when the supplied
finite roots come with the explicit coverage proof. Without coverage, it is a
precise finite-root result and no unlisted world is silently quantified over.

## Gate-19 instance

The known two-edge trace has the recovery profile `T -> N -> T`. Gate 24
computes:

```text
recovery-changing edges = 2
initial position-wise budget = 16
final remaining potential = 4
```

Hence its strong numerical instance is `2 + 4 <= 16`. The initial value `16`
comes from four compiled belief observations, each initially carrying a scope
of four worlds.

## What the result does and does not say

The theorem is a finite resource bound on changes of recovery status. It does
not say that every update changes recovery, that each change costs exactly one
unit, or that the position-wise upper bound is optimal.

Repeated compiler positions may refer to the same agent/world coordinate. The
same strict coordinate loss can then contribute to several position budgets.
This is sound over-approximation: duplicates enlarge the available budget and
cannot falsify the upper bound. It explains why the concrete bound `16` is
substantially larger than the two observed changes.

The result currently covers the repository's dependent finite traces of
admissible conditionalizations. It is not yet a theorem for product update,
arbitrary model transformations, or infinite update sequences.

## Next research question

The natural sharpening is:

> Can the Gate-21 belief observations be quotiented by agent/world coordinate
> so that every recovery-changing edge consumes a strict loss in a finite
> duplicate-free coordinate budget?

If successful, Gate 25 would replace the safe position-wise sum by the sum of
initial scope lengths over unique reachable belief coordinates. It should be
attempted before extending the counting theorem to product updates, because it
tests whether the present looseness is merely compiler multiplicity or hides a
deeper failure of injective resource accounting.

## Verification

```powershell
lake build
lake env lean PEL4/FiniteRecoveryFlipBudgetAxiomAudit.lean
```
