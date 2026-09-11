# Gate 26: abstract finite epistemic descent

## Research question

Which structural property of an epistemic update process is sufficient to
inherit the finite recovery-flip bound without rebuilding the Gate-24/25
counting proof for every concrete update mechanism?

## Answer targeted by this gate

A very small local contract is sufficient.

An update system needs only:

1. a Boolean status `status(s)`;
2. a natural-valued finite potential `Phi(s)`;
3. an update relation `Step(s,t)`; and
4. the one-step inequality

```text
changeCost(status(s), status(t)) + Phi(t) <= Phi(s),
```

where `changeCost` is `1` exactly when the Boolean status changes and `0`
otherwise.

From this local condition alone, every finite update path satisfies

```text
number of status changes already incurred
+ final remaining potential
<= initial potential.
```

Hence

```text
number of status changes <= initial potential,
```

independently of path length.

## Formal abstraction

`RecoveryDescentSystem State` contains four fields:

- `status : State -> Bool`
- `potential : State -> Nat`
- `Step : State -> State -> Prop`
- `step_budget`, the local descent contract above.

`recoveryDescentFollows` describes a finite path through an arbitrary `Step`
relation.  `recoveryChangeCountFrom` counts only edges on which status really
changes, and `recoveryFinalStateFrom` records the final state.

The main theorem is

```text
recoveryDescent_changeCount_add_finalPotential_le
```

with the immediate corollary

```text
recoveryDescent_changeCount_le_initialPotential.
```

A second corollary shows that once potential reaches zero, no admissible finite
continuation can contain another status change.

## Strict descent interpretation

The local contract also yields

```text
status(s) != status(t)  ->  Phi(t) < Phi(s).
```

So a recovery change is not merely counted.  It is a strict descent in a
well-founded natural-valued resource.  This is the abstract core hidden inside
Gates 23-25.

## Connection back to 4PEL

Gate 25 provides exactly the local contract needed here.

`recoveryCoordinateSnapshot` packages a concrete 4PEL model, roots, formula,
and cumulative scope assignment into the two abstract quantities:

- recovery status; and
- duplicate-free coordinate potential.

The bridge theorem

```text
conditionalization_recoveryCoordinateSnapshot_step
```

proves that every admissible conditionalization edge whose cumulative scopes
carry the required concentration hypothesis is a valid step of the abstract
descent system.

Therefore the finite-flipping theorem is no longer conceptually tied to
conditionalization.  Conditionalization is one verified implementation of a
more general resource principle.

## Robot sanity model

The executable Gate-26 toy path uses three snapshots:

```text
(true, 2) -> (false, 1) -> (true, 0)
```

Lean checks that the path follows the descent contract, contains exactly two
status flips, and exhausts exactly two units of potential.

## What this gate proves

Gate 26 proves a sufficient structural criterion for finite recovery
oscillation:

> If every recovery-changing update edge consumes at least one unit of a
> natural-valued potential and the one-step potential budget is respected,
> then no finite path can contain more recovery changes than the initial
> potential.

The theorem is update-agnostic.  Any future update semantics can inherit the
bound by supplying the local descent contract.

## What this gate does not yet prove

This gate does not prove that every interesting epistemic update operation
satisfies the contract.  In particular, product update may introduce new
world/event coordinates and can therefore increase a naive scope-counting
resource.  Product update needs its own resource analysis before it can be
registered as another instance.

Nor does the gate claim that the natural-valued coordinate potential is a
necessary representation for every finitely flipping system.  The result is a
clean sufficient principle, not a characterization theorem.

## Research significance

Gates 23-26 can now be read as a single descent architecture:

```text
Gate 23  recovery change -> strict local scope loss
Gate 24  local losses -> finite positional budget
Gate 25  positional budget -> duplicate-free semantic coordinate budget
Gate 26  concrete coordinate budget -> abstract finite-descent principle
```

The resulting statement is stronger conceptually than a theorem about one
update operator.  It identifies the resource mechanism responsible for finite
recovery oscillation.

## Next research directions

Two natural continuations are now cleanly separated:

1. **Product-update instantiation:** find a product-update resource whose
   one-step budget satisfies the Gate-26 contract despite possible state-space
   expansion.
2. **Characterization question:** investigate when a uniformly finitely
   flipping update system admits a natural-valued descent ranking, and whether
   ordinal-valued resources are needed for infinite but well-founded state
   spaces.

## Verification

```powershell
lake build
lake env lean PEL4/FiniteEpistemicDescentAxiomAudit.lean
```
