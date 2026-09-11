# Gate 21: finite recovery-observation maps

## Research question

Can the recursively relevant sites of a fixed modal formula be compiled into
a finite map, and must every recovery change under conditionalization appear
as a change at one of those sites?

## Exact finite compiler

`recoveryObservationSites m w phi` follows the syntax of `phi` from a starting
world `w`:

- an atom contributes its world/formula observation;
- negation reuses the observations of its body;
- conjunction appends both observation lists;
- belief contributes its own result and recursively visits its body at every
  accessible world;
- knowledge and possibility recursively visit their accessible profiles.

Duplicates are retained because the list records the evaluation tree rather
than a quotient by equality. Since formulas are finite and every accessibility
range is a finite list, the result is finite by construction.

Lean proves the exact characterization

```text
CompositionallyClassicalAt m w phi
iff
every compiled observation is classical in m.
```

Probability integrity then turns the right side into an exact characterization
of compositional recovery on any explicit finite list of starting worlds.

## Stuttering theorem

Conditionalization changes the probability field but preserves valuations,
accessibility, thresholds, and the formula. Therefore the compiled observation
map is structurally identical before and after an update.

Lean proves:

```text
if every compiled observation retains its classical/nonclassical status,
then recovery on the finite roots retains its status.
```

The contrapositive is the main Gate-21 bridge:

```text
every recovery change has a concrete changed observation
inside the finite compiled map.
```

The compiler emits only atomic and belief-result observations. Atomic values
cannot change under probability-only conditionalization because valuations
are fixed. Lean therefore sharpens the result:

```text
every recovery change has a changed belief-result observation
inside the finite compiled map.
```

This is stronger than merely saying that some unspecified part of the model
changed and isolates the only substantive observation kind for the next gate.

## Finite roots versus global recovery

The repository's original `CompositionalRecovery` quantifies over every value
of the ambient type `W`. The base `Model` structure stores a finite `worlds`
list but does not require that list to enumerate every possible `W` value.

Gate 21 therefore introduces `WorldListCovers roots`. With such an explicit
coverage proof, recovery on `roots` is equivalent to global recovery, and every
global recovery change receives a witness in the finite compiled map. Without
coverage, only the stated finite-root theorem is justified.

## Gate-19 instance

For `B(p)` on the four Gate-19 roots, the compiler produces twenty positions:

```text
4 belief-result observations
+
4 roots * 4 accessible atomic observations
= 20 positions.
```

Lean verifies that the list itself is unchanged by the first update. It also
identifies an explicit changed observation: at world `a`, `B(p)` is classical
before conditioning on `q` and nonclassical afterward. Thus the abstract
localization theorem matches the existing `T -> N -> T` witness.

## Gate-22 resolution and remaining numerical work

Gate 21 proves finite localization, not yet a number bounding all changes along
an entire trace. Gate 22 connects the changed compiled belief observation to
the Gate-20 resource budget, but reveals a necessary recursive qualification.

The question posed here was:

> Does every classical/nonclassical change at a compiled belief observation
> require a strict loss of its cumulative positive-evidence support?

Gate 22 answers: either that local scope shrinks strictly, or the belief body
has already changed at an accessible world. The unqualified pointwise claim is
therefore too strong. The next gate must chase inherited body changes through
the finite evaluation tree to a strictly shrinking reachable belief
coordinate; only then can distinct coordinate budgets be summed.

## Verification

```powershell
lake build
lake env lean PEL4/FiniteReachableRecoveryAxiomAudit.lean
```
