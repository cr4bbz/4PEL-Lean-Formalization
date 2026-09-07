# Gate 12: phase nerves under persistent evidence

## Assumption

`FDEInformationLE a b` preserves each evidence bit that is true in `a`.
This is the information order `N <= T,F <= B`, not the truth order.
`PersistentFDEProfile R value` requires this growth along each accessibility
edge. It is an additional assumption on one selected value profile; it is not
imposed on the repository's evaluator or automatically established for every
4PEL formula. Accessibility here is not being identified with elapsed time.

## Verified results

| Frame and profile | Consequence |
|---|---|
| S5, arbitrary profile (Gate 11b) | Every complex with a vertex is realizable when frame and profile may vary |
| S5, persistent profile | Each successor profile is a realized singleton; no phase-contact edges |
| S4, persistent profile | Any T/F contact witness has actual value N |
| S4, persistent profile, face sigma contains T and F | `sigma ∪ {N}` is also a face, at the same witness |
| S4, persistent profile, T/F edge | A filled N/T/F triangle exists |
| S4, persistent profile, T/F/B triangle | A full N/T/F/B tetrahedron exists |

Symmetric accessibility forces constancy because persistence gives information
inequalities in both directions, and the information order is antisymmetric.
Constancy is per accessibility component. Components may differ, and a constant
B component is permitted: persistent inconsistency is not a stability defect.

For the S4 contact rule, a world reaching both T and F must lie below both in
the information order. Only N can do so. Because the world belongs to the
closure of its own fibre, it supplies an N contact as well.

## Sharpness

The four-world model uses one world of each phase. N sees all four worlds;
T, F and B see only themselves. Lean verifies reflexivity, transitivity,
antisymmetry, persistence, and the full phase tetrahedron at N. Thus persistence
does not lower the maximal S4 nerve dimension below three, even on a finite
antisymmetric frame. The model is not symmetric, so it does not contradict
the S5 collapse theorem.

The necessary face-completion rule is not yet presented as a sufficient
classification of all persistent S4 nerves. Constructing arbitrary realizations
under that rule and classifying a fixed frame remain future work.

## Formal evidence

All new declarations are in `PEL4/TopologicalEvidencePersistentNerve.lean`,
root-imported by `PEL4.lean`. Principal theorems:

- `persistent_s5_simplex_iff`
- `persistent_s5_locally_constant`
- `persistent_s5_no_phase_edges`
- `persistent_T_F_contact_is_N`
- `persistent_simplex_T_F_adjoin_N`
- `persistent_T_F_edge_forces_N_triangle`
- `persistent_T_F_B_triangle_forces_tetrahedron`
- `persistent_s4_full_tetrahedron`

Full Lean 4.31.0 CI run 610 passed at
`48147cb76bd8bb45fcb41379d58ae99b5c0d333c` (114 jobs).
The focused axiom reports for S5 classification, face completion, and the
tetrahedron list only `propext`, `Classical.choice`, `Quot.sound`.
No new `sorry`, project axiom, `unsafe`, or `native_decide` proof step is used.
This focused statement does not audit all historical modules.

Manuscript appendix C contains definitions, proofs and limits. Appendices B/C
were rendered together as four pages and visually checked. Existing committed
manuscript PDFs have not been regenerated. No historical novelty priority is
claimed for these results.
