# Project Axiom Audit

Status: cleanup working document.

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
explicit `rfl`, `decide`, or short case-analysis proofs.

Known examples include model normalization and threshold facts in:

- `PEL4/Godel.lean`
- `PEL4/ExFalso.lean`
- `PEL4/Paradoxes/Liar.lean`
- `PEL4/Paradoxes/Lottery.lean`
- `PEL4/Paradoxes/Moore.lean`
- `PEL4/Paradoxes/Cartography.lean`
- `PEL4/Paradoxes/SyntheseExtensions.lean`

This list is a cleanup ledger, not a claim that the listed mathematical facts
are doubtful. The point is that finite decidable obligations should be proved
inside Lean rather than introduced as global constants.

## C. Native-computation dependencies

`native_decide` is not a project-specific mathematical axiom, but it does
enlarge the trusted base from kernel reduction to the Lean compiler and native
evaluator. Source scanning for `axiom` does not reveal this dependency.

The repository currently contains `native_decide` in older finite-model and
case-classification modules. Those results remain useful compiler-checked
artifacts, but must carry `COMPILER-TRUST` rather than being described as
kernel-only results.

The complex-coordinate publication chain has received a focused cleanup:

- three sixteen-case proofs in `ComplexCoordinates.lean` now use `decide`;
- `ComplexBeliefRegions.lean` uses symbolic arithmetic proofs;
- `ComplexRotation.lean` uses `decide`, case analysis, and `omega`;
- `PEL4/ComplexAxiomAudit.lean` reproduces the corresponding `#print axioms`
  output.

## D. Completion criterion

R0.2 is complete when all convenience axioms in concrete finite examples have
been replaced by proof terms and a repository-wide source scan leaves only
explicitly documented substantive prototype axioms.

The remaining axioms after R0.2 should therefore coincide with modules whose
primary status is `AXIOMATIC-PROTOTYPE`.

A later verification gate should also classify every remaining
`native_decide` dependency and replace it where ordinary kernel reduction is
small enough.
