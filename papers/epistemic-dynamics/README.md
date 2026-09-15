# Epistemic Dynamics under Inconsistency

**Research Paper v0.3.0 - 15 September 2026**

Subtitle: *Recovery, Active Experimentation, Model Criticism, and Rational Self-Trust in 4PEL*

This is the independent, newer Epistemic Dynamics paper. It is intentionally separate from `paper/main.tex`, which is the repository's Working Manuscript.

## Formalization snapshot

- Branch: `research/epistemic-self-trust-integration-gate104`
- Commit: `2cf3c12db6aa222a92af2c512ae68aae3fb7a0df`
- Scope: formal development through Gate 104

## Build

From this directory:

```bash
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The paper is modularized into six narrative section files plus the formal result map, verification snapshot, and references. The result map lists the Gate 62-104 extension explicitly.

## Verification boundary

Lean verification certifies the consequences of the encoded definitions and assumptions. Interpretive claims in the paper are kept separate from finite machine-checked witnesses. In particular, Gate 104 is a verified finite self-trust controller, not a universal theorem of epistemic rationality.
