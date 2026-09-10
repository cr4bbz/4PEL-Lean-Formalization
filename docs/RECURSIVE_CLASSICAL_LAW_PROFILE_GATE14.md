# Gate 14: recursive LEM/EFQ profile

## Research question

Do tolerant excluded middle (LEM) and universal LP explosion (EFQ), imposed at
every syntactically and modally relevant formula node, characterize the
compositionally classical sector of 4-PEL?

## Result

Yes. `PEL4/RecursiveClassicalLawProfile.lean` defines modal versions of excluded
middle and direct contradiction and proves locally:

```text
tolerant LEM     iff gap-free
universal LP EFQ iff glut-free
LEM and EFQ      iff value is T or F.
```

The law pair is then traversed through propositional subformulas and through
the accessible operands of belief, knowledge, and possibility. Lean proves:

```text
RecursiveClassicalLawProfileAt m w phi
iff
CompositionallyClassicalAt m w phi.
```

Globally, and with probability integrity, this also gives:

```text
RecursiveClassicalLawProfile m phi
iff
CompositionalRecovery m phi.
```

The first equivalence is purely four-valued and needs no probability
assumption. Probability integrity enters only when semantic classicality is
identified with the threshold-completeness recovery certificate.

## Interpretation boundary

LEM and EFQ do not define every aspect of a logic. The theorem characterizes a
specified recursive semantic fragment of the current 4-PEL language and
consequence readings. It is not yet a proof-system completeness theorem.

## Verification

```powershell
lake build PEL4.RecursiveClassicalLawProfile
lake env lean PEL4/RecursiveClassicalLawProfileAxiomAudit.lean
```

