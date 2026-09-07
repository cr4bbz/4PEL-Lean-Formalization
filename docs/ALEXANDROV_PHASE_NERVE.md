# Alexandrov phase nerves: classification and realization

Research branch: `research/topological-evidence` (PR #2).

## Verified boundary

Gate 11a classifies the nerve of an arbitrary FDE-valued profile on a
reflexive/transitive successor frame. Gate 11b realizes every downward-closed
complex on the four phase labels **with at least one vertex** by a finite
equivalence frame. This is a theorem about arbitrary profiles, not about
probability-threshold profiles on a fixed model.

For a world `w`, define `S(w) = {value(u) | u ∈ R(w)}`. Then:

```
sigma is a phase-nerve simplex iff there exists w with sigma ⊆ S(w).
```

The nerve is the downward closure of the reachable phase profiles. An edge
only gives its own witness; a complete graph need not have a common witness
for all four phases. The pair-world countermodel verifies this distinction.

## Universal realization

For a complex K, use worlds `(tau,q)` with `tau ∈ K` and `q ∈ tau`.
Two worlds are accessible exactly when their face labels `tau` agree.
The actual value at `(tau,q)` is `q`. Thus every world labelled `tau` has
reachable profile exactly `tau`.

The relation is reflexive, symmetric and transitive. In particular, even
S5-frame conditions do not restrict which abstract phase complexes are
realizable when both frame and valuation can vary.

The Boolean-mask implementation explicitly enumerates the world type with
a list of length at most 64. This is a proved conservative bound, not a
minimal-world theorem. Classical decidability is used to filter an arbitrary
proposition-valued input complex; no executable procedure for such an
unspecified predicate is claimed.

## Edge cases

- Missing FDE labels stay missing: no extra vertices are inserted.
- The empty face is included when there is at least one world.
- A complex containing only the empty face has no such realization: any
  world witnesses its own singleton phase.
- An empty world type has a nerve with no faces under the witness-based
  definition used here.
- No antisymmetry or T0 property of the realizing frame is claimed.
- No homotopy-equivalence or nerve-lemma conclusion is claimed.

## Proof map

| Claim | Declaration |
|---|---|
| Local closure = phase reachability | `alexandrov_phase_closure_iff_reachable_phase` |
| Arbitrary simplex classification | `alexandrov_phase_simplex_iff` |
| Exact realization of K | `every_phase_complex_realized` |
| Complete finite world enumeration | `phaseRealizationWorlds_complete` |
| World-list bound | `phaseRealizationWorlds_length_le` |
| Equivalence-frame symmetry | `phaseRealization_symmetric` |
| A world always produces a vertex | `phase_nerve_has_vertex_at_world` |

The first two declarations are in `PEL4/TopologicalEvidenceAlexandrovNerve.lean`;
the remaining ones are in `PEL4/TopologicalEvidenceNerveRealization.lean`.
Both are root-imported by `PEL4.lean`.

Lean Action CI run 606 passed on `54877984dec8ad0cf9b0a1036feb1ef312d0e59f`
(Lean 4.31.0, 113 build jobs). The focused axiom output for the universal
theorem, finite bound and symmetry contains only `propext`, `Classical.choice`
and `Quot.sound`. The new module has no `sorry`, `admit`, project axiom,
`unsafe` or `native_decide` declaration/proof step. This does not audit older
modules repository-wide.

## Research significance and next boundary

The ordinary nerve construction and equivalence-frame ingredients are standard;
no priority claim is made. The contribution here is their exact connection to
four-valued successor profiles and the machine-checked classification.

The next substantive restriction should constrain **admissible value profiles**
or fix the frame, rather than assume S4/S5 alone. Candidate questions are
monotonicity of the two evidence channels, which nerves arise from a fixed
probabilistic threshold model, and minimal numbers of worlds. These are open
in the current formalization.

The mathematical proof and its limitations are added as appendix B in the
LaTeX manuscript. That appendix was separately compiled and visually checked;
the old committed PDF is not an updated render of this research increment.
