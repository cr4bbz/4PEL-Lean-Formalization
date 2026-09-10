# Gate 10: compositional classical recovery

## Research question

Under which local, compositional hypotheses does the recovered classical
fragment survive the full modal language, and when does that recovery transfer
to semantic consequence?

Gate 10 starts from the result of Gates 5--9: classicality is a structural
property of an FDE value, propositional constructors preserve it, belief needs
probability and threshold conditions, and classical antecedents make ST and LP
consequence coincide. The new task is to connect those facts by one recursive
contract for `ModalFormula`.

## Verified initial slice

The implementation is in
`PEL4/CompositionalClassicalRecovery.lean`. Its central predicate is:

```text
CompositionalRecoveryAt m w phi
```

It follows the syntax of `phi`:

- atoms must already have a classical value at the current world;
- negation inherits recovery of its operand;
- conjunction requires recovery of both operands;
- knowledge and raw possibility require recovery of the operand throughout the
  accessible profile;
- belief requires accessible-profile recovery and local threshold
  completeness.

On a `ModelProbabilityIntegrity` model, this contract is sufficient for a
classical modal evaluation:

```text
CompositionalRecoveryAt m w phi
-> IsClassicalValue (evalModal m w phi).
```

The global form quantifies the contract over every world. Constructor theorems
show closure under negation, conjunction, primitive knowledge, and raw
possibility. Belief is closed only when its additional
`BeliefCompleteEverywhere` obligation is supplied. Probability integrity
provides the corresponding consistency side of the threshold boundary.

## Consequence transfer

Gate 10 also introduces model-relative modal LP and ST consequence. For a
globally recovered modal antecedent `phi`:

```text
ModalST_SemanticEntailsIn m phi psi
iff
ModalLP_SemanticEntailsIn m phi psi.
```

The theorem holds for every consequent `psi` in the same model. It does not
require the consequent to be classical: the collapse occurs because positive
support of a classical antecedent already forces its strict value to be `T`.

## Verified boundary

Atomic classicality alone still does not recover threshold belief. The finite
Gate-6 threshold-gap model is reused as a modal counterexample:

```text
AtomicClassicalModel gate6BeliefBoundaryModel
and
not CompositionalRecovery gate6BeliefBoundaryModel (bel p).
```

This is the key separation in the current gate:

```text
classical atoms
!= compositionally recovered modal language
```

The missing ingredient is not a propositional closure law but threshold
completeness for belief.

## Theorem map

| Declaration | Role |
| --- | --- |
| `ModalFormula.CompositionalRecoveryAt` | local recursive recovery contract |
| `evalModal_isClassical_of_compositionalRecovery` | main local soundness theorem |
| `ModalFormula.CompositionalRecovery` | global recovered-fragment predicate |
| `evalModal_isClassical_of_global_compositionalRecovery` | global classical evaluation |
| `ModalFormula.CompositionalRecovery.prop/not/and` | propositional closure |
| `ModalFormula.CompositionalRecovery.know/poss` | modal closure |
| `ModalFormula.BeliefCompleteEverywhere` | explicit belief-side obligation |
| `ModalFormula.CompositionalRecovery.bel` | conditional belief closure |
| `modalST_iff_LP_of_compositionalRecovery` | fragment-relative consequence collapse |
| `gate10_atomicClassical_but_belief_not_recovered` | finite boundary witness |

## Audit and reproduction

```powershell
lake build
lake env lean PEL4/CompositionalClassicalRecoveryAxiomAudit.lean
```

The focused audit covers eleven Gate-10 theorems. On Lean 4.31 they depend only
on Lean's standard logical principles (`propext`, `Classical.choice`, and
`Quot.sound`) and introduce no project-specific or native axioms.

## Current nonclaims

This initial slice does not yet establish:

- necessity or minimality of every clause in the recovery contract;
- an unrestricted global collapse of LP, ST, or classical consequence;
- recovery of belief from atomic classicality alone;
- an independent CPEL model class, proof calculus, or completeness theorem;
- preservation of the recovered fragment under conditionalization or product
  update;
- a syntactic decision procedure for the largest recovered modal fragment.

## Next subgates

The most informative continuation is:

1. prove exact or counterexample-backed necessity results for the knowledge,
   possibility, and belief clauses;
2. characterize update preservation of `CompositionalRecovery`;
3. lift the model-relative consequence result to a clearly delimited class of
   models;
4. compare the semantic contract with a syntactically generated recovered
   fragment;
5. only then connect the result to an independently specified CPEL calculus.

