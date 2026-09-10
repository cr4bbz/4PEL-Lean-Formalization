# Gate 20: bounds on repeated evidence-scope change

## Research question

Can recovery change arbitrarily often along a finite sequence of admissible
conditionalizations, or is the number of changes bounded by the finite evidence
that remains available?

## Result: a sharp local bound

Gate 20 formalizes the cumulative evidence scope at one fixed agent/world
belief site. At every update, that scope is intersected with the positive
extension of the new evidence formula. Since the evidence formula is evaluated
in the actual posterior source model, this construction respects the dependent
update traces introduced in Gate 19.

Lean proves the stronger budget formula

```text
length(final cumulative scope) + number of strict scope shrinkages
<=
length(initial accessibility scope).
```

Consequently, at a fixed local belief site, strict cumulative scope shrinkage
is bounded both by the length of the update trace and by the number of worlds
in the initial accessibility list.

The cardinality bound is sharp. A checked three-world descent removes exactly
one world at each of three steps and reaches the empty scope.

## Relation to Gate 19

The four-world Gate-19 witness has the recovery profile

```text
T -> N -> T
```

and its cumulative local evidence scope follows

```text
[a,b,c,d] -> [a,c] -> [a].
```

Lean therefore computes two strict scope shrinkages for the two recovery
changes in this example. This is an informative alignment, but it is not a
general equivalence theorem.

## Why this does not yet bound recovery flips globally

Recovery is a recursive property of a modal formula. A change may depend on
several belief sites reached at different modal subformulas and accessible
worlds. The current Gate-20 theorem follows one fixed pair `(agent, world)`.
Therefore the local cardinality budget must not be advertised as a bound on
the number of global recovery loss/return transitions.

A global theorem needs two additional bridges:

1. a finite compilation of all belief sites reachable from a fixed modal
   formula and starting world(s);
2. a stuttering theorem showing that a recovery change requires a genuine
   change at one of those compiled local sites.

The finite syntax of formulas and finite accessibility lists make this a
plausible next construction. Gate 20 identifies it as a proof obligation
rather than introducing an unjustified global axiom.

## Answer to the gate question

Strict evidence loss cannot occur arbitrarily often at any fixed local site;
its exact finite resource is the initial scope cardinality. Whether recovery
itself admits the corresponding global bound remains open at this gate. The
right next step is a finite reachable-site compiler and a recovery-stuttering
lemma, not another numerical example.

## Verification

```powershell
lake build
lake env lean PEL4/FiniteUpdateScopeBoundsAxiomAudit.lean
```
