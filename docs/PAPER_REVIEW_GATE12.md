# Paper review after Gate 12

Review date: 2026-09-10  
Reviewed artifact: `paper/main.pdf`, working manuscript version 0.13,
54 pages

## Review outcome

The manuscript is internally coherent through Gate 9, builds reproducibly, and
has no visible clipping, overlap, broken figure, unresolved reference, or
overfull box. It is not yet an up-to-date account of the Lean development: the
formal project now contains Gates 10--13, while the abstract, mechanization
status, conclusion, formal correspondence, and reproduction branch still stop
at Gate 9.

The recommended editorial action is therefore a coordinated version 0.14
integration rather than isolated sentence-level amendments.

## Findings by priority

### P1 -- The manuscript does not yet report the strongest verified result

Gates 12 and 13 prove an exact dynamic recovery boundary. Under prior
`ModelProbabilityIntegrity` and prior `CompositionalRecovery`, recovery after
admissible conditionalization holds if and only if no recursively reachable
belief node realizes the directed gap pattern. This theorem, its Gate-10 and
Gate-11 prerequisites, Gate-13 posterior-integrity closure, and their axiom
audits are absent from version 0.13.

Affected manuscript locations:

- the abstract ends its gate summary at Gate 9;
- Section 10 names the Gate-9 branch and audit as the active development;
- the conclusion's next-step list predates Gates 10--13;
- Appendix A maps claims only through Gate 9;
- the reproduction commands switch to the Gate-9 branch.

This is a currency gap, not a contradiction in the published Gate-9 claims.

### P1 -- The new result must be stated with its two integrity boundaries

The Gate-12 equivalence explains posterior **completeness**, hence the absence
of `N`. At the time of that gate it could not be paraphrased as unconditional
preservation of classical evaluation:

1. prior integrity and prior compositional recovery are hypotheses of the main
   equivalence;
2. Gate 12 did not yet derive full `ModelProbabilityIntegrity` for the updated
   model from the existing `ConditionalizationAdmissible` interface.

Gate 13 has since discharged the second point under prior integrity, without a
new update axiom. The first point remains, and glut exclusion still requires a
classical accessible profile; gap avoidance and glut exclusion are conceptually
distinct even when they compose in the recovered fragment.

### P2 -- Directed endpoint change is not automatically a continuous crossing

`ThresholdRises` and `ThresholdFalls` classify two endpoint decisions:
`false -> true` and `true -> false`. Calling these changes "crossings" is safe
only when the manuscript explicitly distinguishes them from the earlier
rational affine interpolation, where an actual wall-hit parameter is proved.
An admissible discrete update supplies endpoints, not an intermediate history.

The existing manuscript already observes this distinction for Gates 1--9. The
Gate-12 integration should preserve that discipline by using "directed
threshold change" for the general theorem and "wall crossing" only for a path
carrying the relevant interpolation theorem.

### P2 -- Recovery certificates and recovered values need separate prose

Gate 10 defines a recursive compositional certificate; Gate 11 studies its
preservation under update; Gate 12 replaces the posterior belief-completeness
obligation by an exact directional condition. These are not three names for the
same statement. The integration should display the dependency chain explicitly:

```text
prior compositional recovery
+ prior probability integrity
+ no reachable directed gap pattern
<-> posterior compositional recovery certificate
-> posterior classical evaluation only with the required posterior integrity.
```

This distinction is especially important in the abstract and conclusion, where
compressed wording can otherwise hide a shifted quantifier or missing model
hypothesis.

### P2 -- The abstract is too long for a submission-oriented version

The current abstract contains approximately 1,021 whitespace-delimited words
and occupies most of the first two pages. It functions as a gate-by-gate
executive summary, but it obscures the central research claim and will exceed
the abstract limits of many venues. For version 0.14, reduce it to the problem,
method, two or three strongest results, and explicit boundary; move the gate
inventory to the introduction or mechanization section.

### P3 -- Accessibility and PDF metadata remain incomplete

`pdfinfo` reports blank title, author, subject, and keyword fields, and the PDF
is untagged. This does not affect mathematical correctness, but it weakens
discoverability and accessibility. Populate `hyperref` metadata and evaluate a
tagged-PDF workflow before submission.

### P3 -- Appendix typography is acceptable but can be polished

The build log contains underfull-box warnings, concentrated in the long formal
correspondence table. Visual inspection found no overflow or unreadable entry,
so this is not a release blocker. A future pass can shorten labels, rebalance
columns, or allow more deliberate line breaking.

## Visual and build inspection

- all 54 pages were rendered and visually inspected;
- the phase-plane figure is legible and stays inside its page area;
- theorem boxes, tables, equations, bibliography, and page numbers do not
  visibly overlap or clip;
- no blank accidental page was found;
- the final bibliography page has substantial white space, but this is a normal
  consequence of the reference count rather than a layout defect;
- `scripts/check_paper.py --check-committed` rebuilt the paper and confirmed
  version `0.13`, 54 pages, and committed-text agreement;
- the LaTeX log contains no overfull-box or unresolved-reference warning.

## Recommended version 0.14 integration order

1. Add one combined section for Gates 10--13 rather than four disconnected
   historical reports.
2. State the Gate-10 recursive certificate and its classical-evaluation theorem.
3. Present Gate 11 as the preservation/restoration/fracture question.
4. State Gate 12 as the exact oriented answer for posterior gap creation.
5. Add Gate 13's posterior-integrity and positive-mass minimality theorems.
6. Give the three finite witnesses: gap creation, rise-based restoration, and
   classical-to-glut transition.
7. Preserve the distinction between recursive classicality and accidental
   top-level classicality.
8. Update Section 10, Appendix A, abstract, conclusion, branch name, audit
   commands, and version metadata in one change.
9. Shorten the abstract after the technical integration is stable.

## Suggested next paper-level research question

> Under which strengthened finite conditionalization contract does admissible
> update preserve `ModelProbabilityIntegrity`, so that the Gate-12 absence of
> directed gaps and the supermajority exclusion of gluts compose into an exact
> posterior classicality theorem?

This question is preferable to another purely classificatory gate because it
closes the precise assumption gap exposed by the new equivalence and turns the
directional analysis into a stronger preservation theorem.

## Gate-13 follow-up

Gate 13 answers the suggested question more economically than anticipated. No
new conditionalization field is required: prior `ModelProbabilityIntegrity`
and the existing positive-mass admissibility proof derive posterior integrity.
The normalization fields are themselves derivable from positive mass in this
model class. A version-0.14 integration should therefore include Gate 13 and
replace the provisional "strengthened update interface" wording by the exact
prior-integrity theorem documented in
`docs/CONDITIONALIZATION_PROBABILITY_INTEGRITY_GATE13.md`.
