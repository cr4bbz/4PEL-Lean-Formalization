# Dynamic Epistemic Phase Geometry Paper

Working manuscript:

> **From Threshold Belief to Epistemic Phase Geometry: Mechanized Dynamics in a Four-Valued Probabilistic Epistemic Logic**

Author: Julian L. Voigt (cr4bbz)

Current manuscript version: **0.13** (2026-09-09), 54 pages.

Version 0.13 extends the dynamic core through modal-probabilistic refinement,
matroid evidence, circuits and minors, classical recovery, formula-level
recovery, Lockean threshold phases, the induced CPEL split representation, and
recovery transfer to laws and consequence. The current boundary is summarized
in [`../docs/RECOVERY_CONSEQUENCE_TRANSFER_GATE9.md`](../docs/RECOVERY_CONSEQUENCE_TRANSFER_GATE9.md).

Historical version 0.4 implemented the internal peer review recorded in
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

This paper records the research line extended through
`research/recovery-consequence-transfer-gate9`. The following is an organizational
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
-> complete strong model-valued convex paths
-> modal-probabilistic refinement
-> matroid evidence, circuits, and minors
-> structural and formula-level classical recovery
-> Lockean threshold phase classification
-> induced CPEL split representation
-> recovery transfer to laws and consequence.
```

The manuscript is intentionally narrower than the complete 4-PEL repository. Preface conflict topology, Fitch/Church-Fitch, Knower, Sorites, Surprise Examination, and the broader structural-transport program are mentioned only where they clarify the dynamic interpretation.

## Verification boundary

The current branch has passed a fresh local Lean 4.31 `lake build` with 167
jobs. The live central manuscript audit checks 157 declarations, the separate
MPFG audit checks 24 declarations, and the script suite contains six passing
tests. All selected dependency chains use only the standard allow-list
`propext`, `Classical.choice`, and `Quot.sound`, or no axioms. This is not a
repository-wide axiom-freedom claim.

The 54-page `paper/main.pdf` was freshly rendered and its normalized text was
checked against the committed PDF. The historical
[`docs/PAPER_AXIOMS_v0.4.json`](../docs/PAPER_AXIOMS_v0.4.json) remains a versioned
snapshot; current results come from `PEL4/PaperAxiomAudit.lean` and
`scripts/check_paper_axioms.py`.

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
also compares normalized extracted PDF text with the committed render and checks
that this README's version and page count match `main.tex` and the rendered PDF.
CI runs this check independently of the Lean job; these automated checks do not
replace visual inspection of layout or figures.

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
  14_matroid_evidence.tex
  15_matroid_circuits.tex
  16_matroid_minors.tex
  17_classical_recovery.tex
  18_formula_classical_recovery.tex
  19_lockean_threshold_phase_transition.tex
  20_cpel_split_translation_collapse.tex
  21_recovery_consequence_transfer.tex
  A_formal_correspondence.tex
```

The FDE phase figure is generated directly from TikZ source. It visualizes the three verified affine `N -> B` crossing patterns: positive-first, negative-first, and simultaneous crossing at `(c,c)`. The detailed crossing times are kept in a compact legend to avoid annotation overlap inside the support square.

## Next paper gate

The Lean development now includes Gates 10--17. None is yet part of the version
0.13 manuscript. A paper integration should first present Gates 10--13 as the
dynamic recovery chain, then Gates 14--17 as a separate classical-boundary
chain:

```text
recursive LEM + EFQ
-> maximal recursive classical sector
-> independent Boolean modal semantics
-> recovered truth and consequence equivalence.
```

The manuscript must preserve the proved scope: maximality is relative to the
declared recursive-fragment comparison class, and consequence equivalence is
model-relative and recovery-guarded. No proof-system completeness or
unrestricted classical collapse is established. Gate 18 will determine whether
the next manuscript increment should add a sound calculus only or attempt a
full completeness result. Finite update sequences are scheduled after that
decision.

The post-Gate-12 manuscript review, including the visual inspection and the
prioritized version-0.14 integration plan, is recorded in
[`../docs/PAPER_REVIEW_GATE12.md`](../docs/PAPER_REVIEW_GATE12.md).
