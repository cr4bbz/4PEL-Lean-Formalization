# Dynamic Epistemic Phase Geometry Paper

Working manuscript:

> **From Threshold Belief to Epistemic Phase Geometry: Mechanized Dynamics in a Four-Valued Probabilistic Epistemic Logic**

Author: Julian L. Voigt (cr4bbz)

Current manuscript version: **0.4** (2026-09-07), 27 pages.

Version 0.4 implements the internal peer review recorded in
[`docs/PEER_REVIEW_v0.3_to_v0.4.md`](../docs/PEER_REVIEW_v0.3_to_v0.4.md).
It clarifies the weak versus strong model contracts, knowledge dependencies,
interpolation versus update dynamics, simultaneous-hit boundary values, and
the limited semantics of reliability tags. It also adds direct related work,
four Lean boundary checks, and a strict 52-declaration manuscript axiom audit.
The review is AI-assisted, not an independent external referee report.

Version 0.3 adds `sections/13_modal_probabilistic_refinement.tex`: a conservative
six-cell probability refinement, affine coarse projection, and a local
fibre-rigidity boundary for modal stability. This is not a full LET-K+
axiomatization or a new interpretation of the existing knowledge operator.
See `docs/MODAL_PROBABILISTIC_FINE_GRAINING.md` for validation and scope.

## Scope

This paper records the dynamic research line extended on
`research/modal-probabilistic-fine-graining`. The following is an organizational
sequence, not a claim that every later result applies to every earlier witness:

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

Version 0.4 passed a fresh local LaTeX build on 2026-09-07; the 27-page
`paper/main.pdf` has no overfull boxes, undefined references, or font warnings.
The revised Lean sources at `07fbc5193e0f7e43de565158c0eaf0cbb9c08dfb` passed
the full 122-job build, the strict 52-declaration manuscript audit, the separate
24-declaration MPFG audit, and six checker tests in
[CI run 34133500237](https://github.com/cr4bbz/4PEL-Lean-Formalization/actions/runs/34133500237).
Unlike earlier development checks, this revision's Lean validation was performed
in CI because local Lean cannot resolve its installation path in the review
environment. The selected chains use only standard Lean axioms; this is not a
repository-wide axiom-freedom claim. See
[`docs/PAPER_AXIOMS_v0.4.json`](../docs/PAPER_AXIOMS_v0.4.json).

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

The manuscript compares direct probabilistic BD and six-valued evidence work,
but does not claim a new complete calculus or an established priority result.

## Build the paper

From the repository root:

```bash
python3 scripts/check_paper.py
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_paper_axioms.py
python3 scripts/check_mpfg_axioms.py
```

After committing a new PDF, `python3 scripts/check_paper.py --check-committed`
also compares normalized extracted PDF text with the committed render. CI runs
this check independently of the Lean job; text comparison does not replace
visual inspection of layout or figures.

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
  13_modal_probabilistic_refinement.tex
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
