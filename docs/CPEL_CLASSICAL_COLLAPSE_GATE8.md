# Gate 8 — CPEL split representation and classical collapse

## Final scope

Gate 8 gives the existing split translation an explicit Boolean semantics induced by
the same finite 4-PEL model.  It establishes four layers of results:

1. `tr_pos` and `tr_neg` recover the positive and negative FDE support bits exactly.
2. Their pair represents every four-valued evaluation, without a recovery premise.
3. The classical values `T` and `F` are exactly the anti-diagonal where the negative
   translated bit is the complement of the positive translated bit.  Gate-7
   probability recovery therefore collapses the representation to one Boolean bit.
4. LP and strict-to-tolerant semantic consequence are represented exactly in the
   CPEL evaluator induced by 4-PEL models.  Existing ST derivability transports
   soundly through the source soundness theorem.

The consequence bridge is intentionally model-induced.  Gate 8 does not define an
independent CPEL model class or proof calculus and does not claim target soundness,
completeness, canonical-model results, or decidability.

## Principal declarations

- `evalCPEL_translation_bits`
- `eval_eq_evalCPELPair`
- `classicalValue_iff_neg_eq_not_pos`
- `isClassicalValue_iff_splitTranslations_complement`
- `probabilityRecovery_splitTranslations_collapse`
- `probabilityRecovery_eval_reconstructed_from_tr_pos`
- `eval_eq_T_iff_split_strict`
- `LP_SemanticEntails_iff_CPELPositiveSemanticEntails`
- `ST_SemanticEntails_iff_CPELSplitSTSemanticEntails`
- `ST_derivation_sound_in_induced_CPEL`

## Verification

From the repository root:

```powershell
lake build
lake env lean PEL4/CPELClassicalCollapseAxiomAudit.lean
lake env lean PEL4/CPELConsequenceBridgeAxiomAudit.lean
python scripts/check_paper_axioms.py --report paper-axioms.json
python scripts/check_mpfg_axioms.py
python -m unittest discover -s scripts -p 'test_*.py'
python scripts/check_paper.py --check-committed
```

At closure, the full build contains 149 jobs.  The central manuscript audit contains
143 declarations, all within the standard allow-list (`propext`,
`Classical.choice`, `Quot.sound`, or subsets).  The separate MPFG audit contains 24
declarations, and the script test suite contains six tests.  The manuscript renders
to 51 pages without rejected layout or reference warnings.
