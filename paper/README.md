# Dynamic Epistemic Phase Geometry Paper

Working manuscript:

> **From Threshold Belief to Epistemic Phase Geometry: Mechanized Dynamics in a Four-Valued Probabilistic Epistemic Logic**

Author: Julian Voigt

Current manuscript version: **0.1**

## Scope

This paper records the verified dynamic research line developed on `research/preface-case-study`:

```text
K = stability-filtered threshold belief
-> dynamic stability fracture/restoration
-> complete T/F/B/N reachability
-> threshold-side robustness
-> Boolean threshold-square geometry
-> numerical threshold straddling
-> affine unit-interval threshold crossing
-> unique two-wall crossing times
-> crossing-order trichotomy
-> forced intermediate FDE phase for sequential diagonal crossings.
```

The manuscript is intentionally narrower than the complete 4-PEL repository. Preface conflict topology, Fitch/Church-Fitch, Knower, Sorites, Surprise Examination, and the broader structural-transport program are mentioned only where they clarify the dynamic interpretation.

## Verification boundary

The central formal results through

```text
PEL4/ModalDynamicsIntermediatePhase.lean
```

have passed a fresh local Lean 4.31 `lake build` with the module imported through `PEL4.lean`.

The LaTeX manuscript has also passed a fresh local `latexmk -pdf main.tex` build and produces `paper/main.pdf`.

The strongest verified geometric statement concerns the **affine interpolation of signed support masses**. It does **not yet** prove that every intermediate support point is realized by a full admissible probabilistic model. Likewise, no theorem about arbitrary continuous paths or general measure spaces is claimed.

The manuscript also makes no strong novelty claim before a systematic literature audit.

## Build the paper

From the repository root:

```bash
cd paper
latexmk -pdf main.tex
```

or, with a standard LaTeX toolchain:

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

The expected output is:

```text
paper/main.pdf
```

## Structure

```text
main.tex
references.bib
sections/
  01_introduction.tex
  02_semantic_kernel.tex
  03_dynamic_architecture.tex
  04_complete_reachability.tex
  05_robustness_and_square.tex
  06_affine_crossing.tex
  07_crossing_order.tex
  08_intermediate_phases.tex
  09_structural_interpretation.tex
  10_mechanization.tex
  11_related_work_and_limits.tex
  12_conclusion.tex
  A_formal_correspondence.tex
```

## Next paper gate

Before proving full model-path realizability, the finite probability layer itself should be audited and strengthened. The present core records `mu_total` and `mu_empty`, but does not yet package the usual finite-probability laws such as nonnegativity and finite additivity.

The recommended next sequence is therefore:

```text
current finite probability interface
-> strengthen / characterize finite probability structure
-> prove convex rational paths preserve that structure
-> lift affine support crossings to genuine intermediate model states
-> only then consider general continuous or measure-theoretic paths.
```

This avoids obtaining a formally correct but semantically underpowered realizability theorem merely because the current `Model.mu` contract is intentionally lightweight.
