# Verification Policy

Status: normative repository policy for `research/complex-coordinates`.

This document defines how formal results, finite models, prototypes, and research
interpretations are described in 4-PEL. Its purpose is to prevent a successful
Lean build from being mistaken for a uniform claim of proof strength.

The central rule is:

> **Compilation is necessary evidence of formal well-formedness, but compilation
> alone does not determine the epistemic status of a result.**

A module can compile while depending on project-specific `axiom` declarations,
while another can compile from definitions and explicit proof terms alone. The
repository must keep those cases visibly distinct.

---

## 1. Status classes

Every result highlighted in the README, research documentation, papers, or future
machine-readable metadata should use one of the following primary statuses.

### `PROVED`

Use `PROVED` for a theorem whose Lean proof has compiled successfully and whose
logical dependency chain contains no project-specific unproved `axiom`
declarations relevant to the claim.

A `PROVED` result may depend on:

- definitions;
- theorem proofs already satisfying this policy;
- structure fields carrying explicit proofs, such as `Model.mu_total`;
- ordinary Lean logical principles and trusted kernel infrastructure.

A theorem is **not** `PROVED` merely because its declaration uses the keyword
`theorem` or because `lake build` succeeds.

### `FINITE-WITNESS`

Use `FINITE-WITNESS` for a concrete finite model, executable countermodel, or
finite computational witness whose claimed properties are checked by compiled
Lean proof terms or decidable computation.

Typical uses include:

- a finite countermodel refuting an unrestricted modal principle;
- an explicit update model exhibiting a phase transition;
- a finite incidence profile separating two structural summaries.

A finite witness should still avoid project-specific unproved axioms where the
claimed status is meant to be fully verified. If such axioms are essential, use
`AXIOMATIC-PROTOTYPE` instead.

### `AXIOMATIC-PROTOTYPE`

Use `AXIOMATIC-PROTOTYPE` when a formal construction compiles but one or more
substantive properties are supplied by project-specific `axiom` declarations
rather than proved.

This status is appropriate for exploratory formal interfaces and deliberately
incomplete semantics. Such modules are useful research artifacts, but their
axiom-dependent conclusions must not be described as machine-checked theorems
without qualification.

Current examples include the prototype product-update layer, where probability
normalization and relation-preservation results are still postulated.

### `EXPERIMENTAL / INTERPRETIVE`

Use `EXPERIMENTAL / INTERPRETIVE` for:

- executable sketches that do not yet support a theorem-level claim;
- proposed semantic extensions;
- philosophical diagnoses and cross-paradox interpretations;
- working terminology;
- conjectured completeness, correspondence, novelty, or generalization claims
  not yet formalized.

An interpretation can be strongly motivated by `PROVED` results without itself
becoming a Lean theorem.

---

## 2. Secondary labels

Primary status answers "what kind of formal support does this claim have?".
Secondary labels may refine it.

Recommended labels are:

- `GENERAL-THEOREM`: universally quantified theorem rather than a single model;
- `COUNTERMODEL`: witness refuting a general principle;
- `CLASSIFICATION`: theorem or theorem family giving an exact boundary;
- `SUFFICIENCY`: hypotheses are proved sufficient but not known minimal;
- `INDEPENDENCE-WITNESS`: finite witness separating assumptions;
- `RESEARCH-TARGET`: explicitly open formal target;
- `INTERPRETATION`: conceptual reading of formal results;
- `COMPILER-TRUST`: native evaluation is part of the trusted base;
- `NOVELTY-UNCHECKED`: originality has not undergone systematic literature audit.

These labels do not replace a primary status.

---

## 3. What counts as a project-specific axiom?

For this policy, a **project-specific axiom** is a Lean declaration introduced
with `axiom` (or an equivalent unproved constant) to assert a mathematical fact
specific to the 4-PEL development.

Examples include postulated normalization of a placeholder probability update
or postulated preservation of transitivity under a prototype construction.

By contrast, a proof field inside a structure is not automatically an
unproved axiom. For example, a `Model` contains obligations such as:

```lean
mu_total : ∀ i w, mu i w (R i w) = 1
mu_empty : ∀ i w, mu i w [] = 0
```

A concrete model can satisfy these fields by explicit proof. The field expresses
an assumption defining the class of admissible models; the proof supplied by a
particular model is part of that model's certified data.

---

## 4. Convenience axioms are not acceptable in verified examples

Finite examples should not use `axiom` merely to avoid proving decidable
arithmetic or normalization facts.

If Lean can discharge a claim with `rfl`, `decide`, elementary case analysis,
or a short explicit proof, the repository should provide that proof.

### `native_decide` changes the trust boundary

`native_decide` evaluates a decision procedure through Lean's compiled native
code. In Lean 4.31 this is represented by a native-computation axiom rather than
by kernel reduction alone. The kernel still checks the surrounding proof term,
but the result additionally trusts the Lean compiler and native evaluator.

Accordingly, `native_decide` is permitted for finite executable witnesses when
ordinary reduction is impractical, but it must be recorded with the secondary
label `COMPILER-TRUST`. Under this repository's strict policy, such a result is
not promoted to unqualified `PROVED` until the native dependency is removed or
the publication explicitly adopts the enlarged trusted base.

The complex-coordinate audit exposed this distinction concretely. Three
sixteen-case results originally used `native_decide`; they now use `decide`:

- `supportComplexCoord_injective`;
- `truthInformationComplexCoord_injective`;
- `supportComplexCoord_squaredDistance_eq_thresholdWallCount`.

During cleanup, older convenience axioms in finite models should be replaced by
proof terms. Until replacement, documentation should avoid presenting those
modules as axiom-free verified witnesses.

---

## 5. Build status versus verification status

The repository distinguishes at least three notions:

1. **compiles**: Lean accepts the declarations and `lake build` succeeds;
2. **verified under assumptions**: the result is kernel-checked given all of its
   explicit and imported assumptions;
3. **axiom-free project result**: no substantive project-specific unproved axiom
   occurs in the dependency chain relevant to the result.

Only the third notion warrants the unqualified repository label `PROVED` under
this policy.

A future audit tool should expose these distinctions automatically, ideally by
combining source-level scans with Lean dependency information such as
`#print axioms` or an equivalent programmatic query.

### Current source-level audit snapshot

As of the complex-coordinate development, a source scan finds no `sorry` or
`admit`, but it does find explicit project axioms in these older areas:

- `ProductUpdate.lean` and `ProductTheorems.lean`;
- `Paradoxes/Preface.lean` and `Paradoxes/PrefaceSigned.lean`;
- `Paradoxes/SurpriseExamination.lean`;
- `Paradoxes/SyntheseExtensions.lean`.

This inventory is deliberately weaker than a transitive theorem-dependency
audit. It also does not detect native-computation axioms merely by scanning for
the source keyword `axiom`.

The focused complex-coordinate audit is reproduced by
`PEL4/ComplexAxiomAudit.lean`. After the three small computations were changed
to `decide`, the audited results in `ComplexCoordinates.lean`,
`ComplexBeliefRegions.lean`, and `ComplexRotation.lean` have no
project-specific axiom dependency and no `native_decide` dependency. A
repository-wide transitive audit remains open because many older finite-model
modules intentionally still use `native_decide`.

---

## 6. `#eval!` is demonstration, not proof by itself

`#eval!` is valuable for executable examples and diagnostics, but an evaluation
printed during a build is not by itself a theorem declaration.

If an evaluated value supports a research claim that matters to the public
result map, prefer adding a named theorem, for example:

```lean
theorem witness_has_expected_value :
    eval model world phi = FDEValue.T := by
  decide
```

Demonstration-only evaluations should gradually move toward dedicated examples
or experimental modules so that the library build remains a concise formal
verification pass.

---

## 7. Documentation rules

When documenting a result:

- say `Lean-verified` only when the relevant theorem or witness has successfully
  compiled on the active branch and satisfies the intended status criteria;
- say `axiomatic prototype` when a substantive dependency is postulated;
- distinguish a finite witness from a general theorem;
- distinguish sufficiency from necessity or minimality;
- distinguish object-language statements from meta-level interpretations;
- do not state completeness, decidability, correspondence, or novelty as
  established unless the repository or cited literature actually establishes it;
- mark project terminology and philosophical diagnoses as interpretations when
  they are not themselves formal theorems.

---

## 8. Publication rule

A paper or release may contain material from all four status classes, provided
that the classes are not blurred.

Recommended language:

```text
PROVED                    -> "Lean proves ..."
FINITE-WITNESS            -> "Lean verifies a finite model in which ..."
AXIOMATIC-PROTOTYPE       -> "The prototype formalizes ..., assuming ..."
EXPERIMENTAL/INTERPRETIVE -> "We propose / interpret / conjecture ..."
```

Before a result is promoted to a publication headline, its dependency status
should be audited explicitly.

---

## 9. MCP-facing consequence

This taxonomy is intended to become machine-readable. A future 4-PEL MCP layer
should return verification provenance together with theorem content, including
at least:

```text
name
module
primary_status
secondary_labels
uses_project_axioms
axiom_dependencies
related_witnesses
related_research_questions
```

The MCP should therefore answer not only *what a theorem says*, but also *what
kind of formal evidence supports it*.

---

## 10. Cleanup invariant

Repository cleanup must preserve the following invariant:

> Moving, renaming, or reclassifying a file must never silently strengthen the
> scientific status of its contents.

A prototype becomes `PROVED` only when the relevant assumptions are discharged,
not when the file is moved into a more respectable directory.
