# Modal-Probabilistic Fine-Graining of Four-Valued Evidence

Gate: **MPFG-1 - conservative refinement and modal transport**.
Branch: `research/modal-probabilistic-fine-graining`.
Base: `research/finite-fine-grainedness-4pel`, commit `a6db0af` (population Gate 4).
Date: 2026-09-07.
Verification: **PENDING CI**. Do not promote the declarations below to
`PROVED` until the full build and focused assumption audit pass.

## Question and scope

Can we record additional reliability information while preserving the existing
four-valued evidence semantics? Which kinds of stability survive forgetting it?

This first subgate deliberately uses a small semantic layer. It changes neither
`FDEValue`, `ModalFormula`, nor the existing knowledge operator. In particular,
it does not silently identify evidence-stable `K` with ordinary modal box.

## Three levels, not six primitive truth values

Write a normalized nonnegative rational fine profile in the order

\[
q=(t,b,n,f,t_r,f_r)\in\Delta^5_{\mathbb Q}.
\]

The forgetful map and threshold observation are

\[
\pi(q)=(t+t_r,b,n,f+f_r)\in\Delta^3_{\mathbb Q},
\qquad
\beta_c(q)=([c\le t+t_r+b],[c\le f+f_r+b]).
\]

The reliable cells are **tags supplied by an interpretation**, not proofs that
the corresponding empirical claims are true. Untagged does not mean unreliable.
The six cells are an evidence refinement; no LET truth tables are asserted.
The older unrestricted `EvidenceStatus` can represent reliable gluts and has
more than six states. `EvidenceCell.toEvidenceStatus` chooses a six-state subset;
it does not replace or classify the whole older type.

`FourCellProbability` is reused from the population-axiology branch. This is an
evidence simplex, not the population-outcome simplex. Likewise, a fine-graining
of cells is not the same assumption as finite-path Finite Fine-Grainedness.

## Acceptance map

The identifiers below live in `PEL4.ModalProbability` (abbreviated `MP`).

| Target | Lean declaration | Intended status after validation |
| --- | --- | --- |
| Every coarse profile has an untagged lift | `SixCellProbability.coarse_untagged` | PROVED |
| Signed support and threshold belief survive projection | `coarse_positive`, `coarse_negative`, `threshold_coarse` in `SixCellProbability` | PROVED |
| Convex mixing preserves six-cell normalization/nonnegativity | `mixSix` and its proof fields | PROVED |
| Projection is affine | `coarse_mix` | PROVED |
| Mixing then forgetting preserves raw belief | `mixture_belief_commutes` | PROVED |
| Reliability cannot be recovered from the coarse profile | `SixCellProbability.no_reliability_reconstruction` | PROVED, using a FINITE-WITNESS |
| Essential/accidental status are meta-level complements | `accidental_iff_not_essential` | PROVED |
| Fine stability descends under any projection | `stable_projects` | PROVED |
| Exact lifting boundary is local fibre rigidity | `stable_iff_coarse_and_fibre_rigid` | PROVED, CLASSIFICATION |
| Coarse change implies fine change | `coarse_accident_lifts` | PROVED |
| Raw status modalities and existing K interpretation are unchanged | `threshold_modalities_commute`, `existing_K_stability_commutes`, `existing_K_value_commutes` | PROVED |
| Finite-chain bridge requires edgewise status preservation | `finite_chain_preserves_threshold` | PROVED, conditional |
| Even S5 geometry does not restore lost reliability | `coarse_stable_fine_accidental`, `probability_profile_projection_hides_instability`, `everywhere_s5` | FINITE-WITNESS |
| Stable B can hide changing glut mass | `stable_B_does_not_mean_constant_mass` | FINITE-WITNESS |
| Refinement retains a B/N nontriviality witness | `refinement_retains_B_and_N` | FINITE-WITNESS |

## Main transport boundary

For a relation R, an observation v and a projection pi, define

\[
\mathrm{Stable}(v,w)\iff\forall u\,(Rwu\Rightarrow v(u)=v(w)).
\]

Then

\[
\mathrm{Stable}(v,w)\iff
\mathrm{Stable}(\pi\circ v,w)\land\mathrm{FibreRigid}(v,\pi,w),
\]

where fibre rigidity says that every accessible fine state with the same coarse
observation as the current state actually equals the current fine state.
This is an exact local decomposition, not a global injectivity claim and not
an automatic guarantee of rigidity. It needs no modal frame axioms.

The current-state predicate differs from homogeneity over a nonreflexive
accessible range. The bridge to the existing Boolean `modalAccessibleValueStable`
is therefore stated separately, without equating those two definitions.

`EssentialAt R v s w` is conditional: if the current status is s, every
accessible status is s. It can hold vacuously when the current status is not s.
`AccidentalAt` requires the current status s and an accessible different status.
These are classical meta-level propositions, not a new FDE negation theorem.

## Witnesses that prevent overinterpretation

1. All mass in untagged T and all mass in reliability-tagged T project to the
   same pure-T profile. Their reliable masses are 0 and 1. Thus there is no
   function of the four coarse masses that recovers reliable mass for every
   fine profile.
2. Put those profiles at two mutually accessible worlds. The coarse profile is
   constant; the fine profile is not. The universal relation is reflexive,
   transitive and Euclidean, so imposing S5-style geometry does not repair this.
3. Pure B and `(0,3/4,1/4,0)` both threshold to B at c=3/5, but their glut masses
   differ. Even four-cell mass stability is strictly stronger than categorical
   stability in this witness.

Thus the downward implications hold, while reverse implications fail:

**fine-profile stability -> coarse-profile stability -> threshold-status stability**.

Projection/threshold commutation in this gate is deliberately definitional:
the fine raw belief is specified to sum the same coarse fibres. It establishes
compatibility of this chosen extension, not a completeness or novelty theorem.
Thresholding itself is not affine. The substantive algebraic result is affine
projection; the substantive negative results locate its information loss.

## Literature and correction of the initial proposal

- Coniglio and Rodrigues, *On six-valued logics of evidence and truth expanding
  Belnap-Dunn four-valued logic*, [arXiv:2209.12337](https://arxiv.org/abs/2209.12337).
  The six-valued base predates the August 2026 probability preprint.
- Borja Macias, Coniglio and Hernandez-Tello, *Probabilities beyond Belnap-Dunn
  logic: dealing with gaps, gluts and reliability*,
  [arXiv:2608.20228](https://arxiv.org/abs/2608.20228), submitted 2026-08-20.
  Its abstract motivates the probability layer; this gate does not reproduce
  its axiomatization, completeness proof, or Jeffrey update.
- Petrukhin, *Essence and Accident Modalities Meet Belnapian Truth Values*,
  [doi:10.1007/s11225-026-10250-z](https://doi.org/10.1007/s11225-026-10250-z),
  published 2026-07-15. Here only the positive status-persistence intuition is
  used; the paper's full four-valued operators and hypersequents are not formalized.
- Piazza and Tesi, *Inside Classical Logic: Truth, Contradictions, Fractionality*,
  [doi:10.1007/s11225-025-10168-y](https://doi.org/10.1007/s11225-025-10168-y),
  online 2025-02-13. Its proof-decomposition fractions are not automatically
  evidence probabilities. A comparison requires an explicit representation
  theorem; no equality between those quantities is assumed here.

## Next subgates

1. **MPFG-2: reliability-sensitive updates.** Define normalized updates with
   explicit nonzero denominators. Prove projection commutation for likelihoods
   constant on each coarse fibre, and a counterexample when this fails. Keep
   Bayesian conditioning and Jeffrey replacement of cell weights distinct.
2. **MPFG-3: probability-one versus necessity.** For finite, nonnegative,
   normalized world weights, isolate the full-support assumption needed to
   infer universal accessibility truth from probability one. Exhibit a
   zero-weight accessible counterworld when full support is omitted.
3. **MPFG-4: generated reliability.** Replace uninterpreted tags by a justified
   reliability model and check its interaction with existing `K`; optionally
   define an object-language extension with a conservative embedding.
4. **Separate representation problem.** Relate proof-theoretic fractional
   values to evidence probabilities only after specifying a semantics-preserving
   map. No completeness or originality claim is attached to MPFG-1.

## Reproduction

```bash
git fetch origin
git switch research/modal-probabilistic-fine-graining
lake build
lake env lean PEL4/ModalProbability/AxiomAudit.lean
```

The focused audit must contain no project-specific axioms, `sorryAx`, or native
decision axioms. Ordinary Lean principles such as `propext` and `Classical.choice`
are reported separately from project assumptions. Legacy axioms elsewhere in
the repository are not removed or silently reclassified by this gate.
