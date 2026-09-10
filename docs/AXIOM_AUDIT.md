# Project Axiom Audit

Status: verified cleanup ledger for
`research/classical-calculus-soundness-gate18`.

Current source inventory: **24 project-specific axiom declarations**.

This file tracks project-specific `axiom` declarations separately from ordinary
structure assumptions and Lean's trusted logical infrastructure.

The audit is intentionally conservative: a declaration remains listed until it
has been replaced by a proof term or moved into an explicitly axiomatic
prototype layer.

## A. Substantive prototype axioms

These axioms express mathematical behavior that is not yet implemented or
proved and therefore must remain classified as `AXIOMATIC-PROTOTYPE`.

### Product update

`PEL4/ProductUpdate.lean`

- `product_mu_total`
- `product_mu_empty`

`product_mu` itself is still a placeholder implementation, so these
normalization properties are substantive assumptions rather than proof
shortcuts.

`PEL4/ProductTheorems.lean`

- `product_transitive_preservation`
- `product_euclidean_preservation`

These relation-preservation statements are currently postulated for the
prototype.

## B. Convenience axioms scheduled for elimination

These declarations occur in concrete finite examples and should be replaced by
explicit `rfl`, `decide`, `native_decide`, or short case-analysis proofs.

The remaining 20 convenience axioms are located in:

- `PEL4/Paradoxes/Preface.lean` — 4 normalization/threshold declarations;
- `PEL4/Paradoxes/PrefaceSigned.lean` — 4 normalization/threshold declarations;
- `PEL4/Paradoxes/SurpriseExamination.lean` — 4 normalization/threshold declarations;
- `PEL4/Paradoxes/SyntheseExtensions.lean` — 8 normalization/threshold declarations.

This list is a cleanup ledger, not a claim that the listed mathematical facts
are doubtful. The point is that finite decidable obligations should be proved
inside Lean rather than introduced as global constants.

## C. Completion criterion

R0.2 is complete when all convenience axioms in concrete finite examples have
been replaced by proof terms and a repository-wide source scan leaves only
explicitly documented substantive prototype axioms.

The remaining axioms after R0.2 should therefore coincide with modules whose
primary status is `AXIOMATIC-PROTOTYPE`.

## D. Reproduce the inventory

From the repository root:

```powershell
python scripts/check_project_axioms.py
```

The checker verifies both names and source locations. Focused theorem dependency
audits remain authoritative for deciding whether a particular result depends on
any of these declarations. A source inventory alone does not establish
dependency.

## E. Gates 14--18 focused audits

The five classical-boundary audit modules inspect 35 selected declarations:

- Gate 14: 8 recursive LEM/EFQ declarations;
- Gate 15: 7 maximality and finite-boundary declarations;
- Gate 16: 7 independent-semantics and comparison declarations;
- Gate 17: 6 truth/consequence equivalence declarations.
- Gate 18: 7 calculus-soundness, transfer, and boundary declarations.

All reported dependencies stay inside the standard repository allow-list
`propext`, `Classical.choice`, and `Quot.sound`, or subsets thereof. No Gate
14--18 theorem depends on a project-specific axiom or a native-decision axiom.
