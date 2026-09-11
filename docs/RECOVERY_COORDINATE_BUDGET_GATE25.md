# Gate 25: duplicate-free recovery coordinate budget

## Research question

Can the Gate-24 position-wise recovery budget be quotiented by semantic
`(agent, world)` coordinate so that repeated compiler occurrences no longer
multiply the same finite evidence resource?

## Answer targeted by this gate

Yes, provided the Gate-23 causal witness can be projected from a compiled
belief occurrence to its owning `(agent, world)` coordinate.  Gate 23 already
supplies exactly that witness: a recovery change yields a belief observation
`bel i body` at a world `w` whose cumulative evidence scope shrinks strictly.
The body is irrelevant to the local scope resource, which is owned by `(i,w)`.

Gate 25 therefore adds a duplicate-free coordinate compiler and aims at the
strong invariant

```text
recovery changes already incurred
+ final remaining unique-coordinate potential
<= initial unique-coordinate potential.
```

Consequently,

```text
number of recovery-changing edges
<= sum of initial accessibility-scope lengths
   over unique reachable belief coordinates.
```

Unlike Gate 24, repeated syntactic occurrences of the same belief coordinate
cannot enlarge this budget.

## Formal construction

`recoveryObservationCoordinateKey` projects each Gate-21 observation to either

- `some (i, w)` for a belief observation at agent/world coordinate `(i,w)`, or
- `none` for an atomic observation.

`none` is an inert zero-resource key.  `dedupRecoveryKeys` removes repeated
keys without adding a library dependency.  The resulting
`recoveryCoordinateKeysFrom` is thus a finite duplicate-free quotient of the
exact recovery compiler at the level relevant to evidence-scope consumption.

For every unique coordinate, Gate 20 supplies the one-step arithmetic fact:
strict shrinkage costs at least one unit of scope length.  Gate 23 supplies a
strictly shrinking coordinate whenever recovery changes.  Summing those
coordinate inequalities and inducting over the existing dependent finite
conditionalization trace yields the trace-level budget.

## Why quotienting is legitimate

Two different formulas may inspect belief at the same `(agent, world)` pair.
For conditionalization, the next local cumulative scope is determined by the
current scope, the agent, the world, and the evidence formula.  It does not
depend on the body of the inspected belief formula.  Hence several compiler
occurrences at the same `(i,w)` are not independent consumable resources.
They are multiple observations of one semantic scope.

## Interpretation

Gate 24 established finite flipping with a safe syntactic over-approximation.
Gate 25 tests whether the finiteness phenomenon is genuinely structural.  A
successful proof shows that the resource can be attached to unique semantic
belief coordinates rather than syntax-tree multiplicity.

The result still does not claim optimality.  A single recovery change may
cause several unique coordinates to shrink, and a strict shrink may remove
more than one world.  The theorem charges only the minimum unit needed for the
upper bound.

## Scope

The theorem remains about finite admissible conditionalization traces.  It
adds `[DecidableEq Ag]` because semantic coordinates must be deduplicated.
Atomic observations remain in the compiler for exact recovery evaluation but
carry no probabilistic scope budget.

## Next research question

Once the coordinate theorem is established, the next abstraction is:

> Which properties of an arbitrary epistemic update relation are sufficient
> for the same finite-flipping result, independently of conditionalization?

Gate 26 should isolate a generic finite-descent contract in which every
recovery-status change consumes at least one unit of a natural-valued
potential.  Conditionalization should then appear as one verified instance of
the contract rather than as part of the counting proof itself.

## Verification

```powershell
lake build
lake env lean PEL4/RecoveryCoordinateBudgetAxiomAudit.lean
```
