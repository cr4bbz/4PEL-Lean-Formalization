# Dynamic Epistemic Phase Geometry Paper

Working manuscript:

> **From Threshold Belief to Epistemic Phase Geometry: Mechanized Dynamics in a Four-Valued Probabilistic Epistemic Logic**

Author: Julian Voigt

Current manuscript version: **0.5**

## Scope

This paper records the verified dynamic research line currently developed on
`research/complex-coordinates`:

```text
K = stability-filtered threshold belief
-> dynamic stability fracture/restoration
-> complete T/F/B/N reachability
-> threshold-side robustness
-> Boolean threshold-square geometry
-> complex support and truth/information coordinates
-> four-cell balance decomposition and exact glut criterion
-> exact complex-region classification of T/F/B/N
-> conflation as conjugation and quarter turns as multiplication by i
-> rotation of evidence masses and lossless (total,z,h) reconstruction
-> numerical threshold straddling
-> affine unit-interval threshold crossing
-> unique two-wall crossing times
-> crossing-order trichotomy
-> forced intermediate FDE phase for sequential diagonal crossings
-> finite probability integrity
-> weight-generated finite measures
-> convex rational probability simplex
-> complete strong model-valued convex paths
-> affine positive/negative support masses for probability-free formulas.
```

The manuscript is intentionally narrower than the complete 4-PEL repository. Preface conflict topology, Fitch/Church-Fitch, Knower, Sorites, Surprise Examination, and the broader structural-transport program are mentioned only where they clarify the dynamic interpretation.

## Verification boundary

The central dynamic and probability-path results through

```text
PEL4/ConvexModelSupport.lean
```

have passed fresh local Lean 4.31 `lake build` checks with the modules imported through `PEL4.lean`.

Version 0.5 adds the verified rotation-symmetry layer, corrects the trust
classification of `native_decide`, and records the focused complex-coordinate
axiom audit. The paper treats the full dihedral-group action and the exact
integer image of the evidence simplex as open formalization targets.
The manuscript source and rendered PDF have passed a fresh build and visual
inspection on the feature branch.

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

Two boundaries remain explicit. First, for a modal formula containing
probabilistic belief, its positive or negative support event may itself vary
with the path parameter. The probability-free fragment is verified, but a
maximal fragment containing `bel` is not. Second, the convex intermediate
models are not claimed to arise by admissible conditionalization of the source
model. No theorem about arbitrary continuous paths or general measure spaces
is claimed.

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
  complex_coordinate_geometry.tex
sections/
  01_introduction.tex
  02_semantic_kernel.tex
  03_dynamic_architecture.tex
  04_complete_reachability.tex
  05_robustness_and_square.tex
  05_complex_coordinates.tex
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

The next mathematical step is now a **packaged complex model-path lift**.

The recommended sequence is:

```text
verified convex strong model path
-> verified probability-free support-event invariance
-> verified affine positive and negative formula-support masses
-> package both masses into an affine truth/information coordinate
-> lift crossing-order and intermediate-phase theorems to genuine model states
-> formalize the simplex-to-diamond projection and its fibers
-> separately study update-generated paths
-> only then consider arbitrary continuous or measure-theoretic paths.
```

This keeps three notions distinct:

```text
valid model-valued path
formula-support path
conditionalization-generated path.
```
