# Repository map

This document is the entry point for repository structure and development status.
Mathematical details belong in the topic-specific gate documents; verification
terminology is governed by `docs/VERIFICATION_POLICY.md`.

## Active development baseline

- Branch: `research/recovery-causal-descent-gate23`
- Lean toolchain: `leanprover/lean4:v4.31.0`
- Root library target: `PEL4`
- Current verified gate: Gate 23, recursive recovery causal descent

The branch is a development baseline, not a claim that every independent
research branch has already been merged. In particular, the Alexandrov and
persistent phase-nerve modules on `research/topological-evidence` are not part
of this branch.

## Research sequence

```text
core four-valued probabilistic epistemic logic
-> dynamic threshold and model-path geometry
-> modal-probabilistic fine graining
-> finite fine-grainedness and population prospects
-> matroid evidence, topology, circuits, and minors
-> value-level classical recovery
-> formula- and modal-level classical recovery
-> Lockean threshold phase classification
-> induced CPEL split representation and consequence bridge
-> recovery transfer to laws and consequence (Gate 9)
-> compositional modal recovery and consequence collapse (Gate 10)
-> dynamic preservation and restoration/fracture of recovery (Gate 11)
-> directional gap/glut patterns and recursive recovery boundary (Gate 12)
-> quotient-measure integrity and exact posterior compositional classicality (Gate 13)
-> recursive LEM/EFQ characterization (Gate 14)
-> maximality and necessity of the recursive classical fragment (Gate 15)
-> independent Boolean probabilistic-epistemic semantics (Gate 16)
-> recovered truth and consequence equivalence (Gate 17)
-> independent classical calculus and recovered soundness transfer (Gate 18)
-> finite conditionalization traces, first loss, and recovery return (Gate 19)
-> sharp local evidence-scope shrinkage bounds (Gate 20)
-> exact finite recovery-observation maps and stuttering (Gate 21)
-> posterior concentration and strict-shrink-or-body-change bridge (Gate 22)
-> recursive localization at a strictly shrinking belief site (Gate 23)
```

The latest gate boundary is documented in
`docs/RECOVERY_CAUSAL_DESCENT_GATE23.md`.
The corresponding manuscript currency and layout review is documented in
`docs/PAPER_REVIEW_GATE23.md`.

## Directory responsibilities

| Path | Responsibility |
| --- | --- |
| `PEL4.lean` | Root import surface for the main Lean library |
| `PEL4/` | Formal definitions, theorems, finite witnesses, and focused axiom audits |
| `PEL4/PopulationAxiology/` | Finite fine-grainedness and population-prospect bridge |
| `PEL4/ModalProbability/` | Six-cell probabilistic refinement and status transport |
| `PEL4/Paradoxes/` | Paradox-specific models and theorem families |
| `docs/` | Research gates, status maps, verification policy, and interpretation boundaries |
| `paper/` | Current LaTeX manuscript and committed PDF |
| `scripts/` | Manuscript, audit, and regression checks used by CI |
| `visualization/` | Standalone explanatory plotting scripts |

## Verification entry points

From the repository root:

```powershell
lake build
lake env lean PEL4/RecoveryCausalDescentAxiomAudit.lean
lake env lean PEL4/RecoveryScopeStutteringAxiomAudit.lean
lake env lean PEL4/FiniteReachableRecoveryAxiomAudit.lean
lake env lean PEL4/FiniteUpdateScopeBoundsAxiomAudit.lean
lake env lean PEL4/FiniteUpdateRecoveryAxiomAudit.lean
lake env lean PEL4/ClassicalModalCalculusAxiomAudit.lean
lake env lean PEL4/RecoveredClassicalConsequenceEquivalenceAxiomAudit.lean
lake env lean PEL4/IndependentClassicalModalSemanticsAxiomAudit.lean
lake env lean PEL4/MaximalClassicalLawFragmentAxiomAudit.lean
lake env lean PEL4/RecursiveClassicalLawProfileAxiomAudit.lean
lake env lean PEL4/ConditionalizationProbabilityIntegrityAxiomAudit.lean
lake env lean PEL4/DirectionalThresholdRecoveryAxiomAudit.lean
lake env lean PEL4/DynamicCompositionalRecoveryAxiomAudit.lean
lake env lean PEL4/CompositionalClassicalRecoveryAxiomAudit.lean
python scripts/check_project_axioms.py
lake env lean PEL4/PopulationAxiology/AxiomAudit.lean
python scripts/check_mpfg_axioms.py
python -m unittest discover -s scripts -p 'test_*.py'
python scripts/check_paper_axioms.py --report paper-axioms.json
python scripts/check_paper.py --check-committed
```

`lake build` checks the modules imported through `PEL4.lean`. Three large audit
surfaces are intentionally executed separately by CI:

- `PEL4/PopulationAxiology/AxiomAudit.lean`;
- `PEL4/ModalProbability/AxiomAudit.lean`;
- `PEL4/PaperAxiomAudit.lean`.

`PEL4/Paradoxes/Scratch.lean` is exploratory and intentionally outside both the
root build and the CI audit surface.

The top-level files `FourNPEL.lean`, `FourNPEL_Theorems.lean`, `Test.lean`, and
`test_rat.lean` are historical or local experiments and are not part of the
Lake default target. The `FourNPEL` pair imports Mathlib, while the main `PEL4`
library intentionally does not.

## Status sources

Use the following order when status documents disagree:

1. compiled Lean declarations and focused `#print axioms` audit modules;
2. the current gate document;
3. `docs/RESEARCH_QUESTIONS.md`;
4. the root and paper READMEs;
5. historical review and snapshot documents.

Historical files remain useful provenance, but their version numbers and build
counts are not the current repository status.

## Current cleanup boundary

The repository contains 24 project-specific `axiom` declarations. Four belong
to the explicit product-update prototype; twenty are convenience axioms in
older finite examples. Their exact locations are maintained in
`docs/AXIOM_AUDIT.md` and enforced by `scripts/check_project_axioms.py`.

No branch merge, module move, or theorem-status promotion should be performed
as part of documentation cleanup. Those operations require their own build and
dependency review.
