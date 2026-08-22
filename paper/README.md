# Dynamic Epistemic Phase Geometry Paper

Working manuscript:

> **From Threshold Belief to Epistemic Phase Geometry: Mechanized Dynamics in a Four-Valued Probabilistic Epistemic Logic**

Author: Julian Voigt

Current manuscript version: **0.2**

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
-> forced intermediate FDE phase for sequential diagonal crossings
-> finite probability integrity
-> weight-generated finite measures
-> convex rational probability simplex
-> complete strong model-valued convex paths.
```

The manuscript is intentionally narrower than the complete 4-PEL repository. Preface conflict topology, Fitch/Church-Fitch, Knower, Sorites, Surprise Examination, and the broader structural-transport program are mentioned only where they clarify the dynamic interpretation.

## Verification boundary

The central dynamic and probability-path results through

```text
PEL4/ConvexModelPath.lean
```

have passed fresh local Lean 4.31 `lake build` checks with the modules imported through `PEL4.lean`.

The LaTeX manuscript previously passed a fresh local `latexmk -pdf main.tex` build and produced `paper/main.pdf`. Because version 0.2 adds a new model-path section and revises several existing sections, the updated manuscript should be rendered again after pulling the latest branch.

The stronger probability development now verifies:

```text
FiniteProbabilityIntegrity
-> weight-generated valid finite measures
-> convex interpolation preserves finite distributions
-> every fixed event mass is affine
-> every rational interpolation point yields a StrongProbabilityModel
-> worlds, R, val, and c remain fixed along the model path.
```

This closes the model-existence gap for **weight-generated strong endpoint models on a common semantic skeleton**.

Two boundaries remain explicit. First, for an arbitrary probability-sensitive modal formula, its positive or negative support event may itself vary with the path parameter, so the fixed-event affine theorem does not automatically yield affine formula-support mass. Second, the convex intermediate models are not claimed to arise by admissible conditionalization of the source model. No theorem about arbitrary continuous paths or general measure spaces is claimed.

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
  09_model_path_realizability.tex
  09_structural_interpretation.tex
  10_mechanization.tex
  11_related_work_and_limits.tex
  12_conclusion.tex
  A_formal_correspondence.tex
```

The FDE phase figure is generated directly from TikZ source. It visualizes the three verified affine `N -> B` crossing patterns: positive-first, negative-first, and simultaneous crossing at `(c,c)`. The detailed crossing times are kept in a compact legend to avoid annotation overlap inside the support square.

## Next paper gate

The next mathematical step is now a **formula-level model-path lift** rather than model existence itself.

The recommended sequence is:

```text
verified convex strong model path
-> prove atomic support events are fixed along the path
-> extend to a path-invariant / probability-free modal fragment
-> identify modalPositiveBeliefMass and modalNegativeBeliefMass with affine fixed-event masses
-> lift crossing-order and intermediate-phase theorems to genuine model states
-> separately study update-generated paths
-> only then consider arbitrary continuous or measure-theoretic paths.
```

This keeps three notions distinct:

```text
valid model-valued path
formula-support path
conditionalization-generated path.
```
