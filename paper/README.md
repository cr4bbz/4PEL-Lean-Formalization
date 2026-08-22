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

The stronger compatibility layer in

```text
PEL4/FiniteProbabilityIntegrity.lean
```

has likewise passed a fresh local Lean 4.31 build. It adds nonnegativity, event extensionality, monotonicity, disjoint finite additivity, duplicate-free supports, empty mass zero, and total mass one as an explicit stronger contract. Existing witness models are not automatically promoted to this stronger layer.

The strongest verified geometric statement in the manuscript itself concerns the **affine interpolation of signed support masses**. It does **not yet** prove that every intermediate support point is realized by a full admissible probabilistic model. Likewise, no theorem about arbitrary continuous paths or general measure spaces is claimed.

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
figures/
  fde_phase_geometry.tex
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

The FDE phase figure is generated directly from TikZ source. It visualizes the three verified affine `N -> B` crossing patterns: positive-first, negative-first, and simultaneous crossing at `(c,c)`. The detailed crossing times are kept in a compact legend to avoid annotation overlap inside the support square.

## Next paper gate

Finite probability integrity is now verified as a compatibility layer. The next mathematical step is to generate local probability measures constructively from nonnegative rational world weights and prove the integrity laws once for that constructor.

The recommended sequence is therefore:

```text
verified finite probability integrity contract
-> weight-generated finite probability measures
-> generic integrity theorem for the weight constructor
-> convex rational interpolation of valid weight vectors
-> lift affine support crossings to genuine intermediate model states
-> only then consider general continuous or measure-theoretic paths.
```

This avoids obtaining a formally correct but semantically underpowered realizability theorem merely because the legacy `Model.mu` contract is intentionally lightweight.
