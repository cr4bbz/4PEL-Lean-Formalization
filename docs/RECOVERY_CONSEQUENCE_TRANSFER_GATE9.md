# Gate 9 — Recovery transfer to laws and consequence

## Research question

Starting from Gate 8's exact split representation and classical anti-diagonal, which
classical laws and consequence collapses follow from semantic recovery conditions?

The gate deliberately distinguishes:

1. one formula value at one model/world point;
2. one formula throughout a fixed model;
3. consequence quantified over the unrestricted class of all 4-PEL models.

## Verified core

For a formula value `v` at one point:

```text
tolerant LEM                  iff v is gap-free
universal value-level LP EFQ iff v is glut-free
strict LEM                    iff v is classical (T or F)
classical                     iff tolerant LEM and universal LP EFQ
```

In Gate 8's split CPEL coordinates `(p,n)`, these become:

```text
tolerant LEM iff p or n
LP EFQ       iff not (p and n)
strict LEM   iff n = not p
```

`Formula.ProbabilityRecoveryAdmissible` under `ModelProbabilityIntegrity` transfers
to strict LEM and universal LP explosion at every world of the chosen model.

For consequence, `LP_SemanticEntailsIn` and `ST_SemanticEntailsIn` quantify only over
worlds of one fixed model.  They coincide whenever the antecedent is classical
throughout that model.  The analogous globally quantified relations coincide when
restricted pointwise to classical antecedent evaluations; no classicality premise on
the consequent is needed.

This antecedent-classical-restricted collapse is not unrestricted global classical
consequence.  Its weaker semantic test validates strictly more formula pairs than
unrestricted LP consequence.  Direct contradiction entails every formula under ST
because it is never strictly `T`.
Under LP, a one-world `B`/`F` countermodel still refutes explosion.  The theorem
`classicalRestricted_explosion_not_global` records both the recovered validity and
the unrestricted failure.

## Principal declarations

- `tolerantLEMAt_iff_gapFreeAt`
- `strictLEMAt_iff_classicalAt`
- `universalLPExplosionAt_iff_glutFreeAt`
- `classicalAt_iff_tolerantLEMAt_and_universalLPExplosionAt`
- `tolerantLEMAt_iff_split_complete`
- `universalLPExplosionAt_iff_split_consistent`
- `strictLEMAt_iff_split_complement`
- `strictLEMIn_of_probabilityRecoveryAdmissible`
- `universalLPExplosionIn_of_probabilityRecoveryAdmissible`
- `ST_iff_LP_SemanticEntailsIn_of_classicalAntecedent`
- `classicalRestricted_ST_iff_LP`
- `LP_SemanticEntails_implies_classicalRestricted`
- `contradiction_ST_SemanticEntails`
- `classicalRestricted_explosion_not_global`

## Non-claims

Gate 9 does not establish:

- completeness of the existing ST derivation system;
- a proof system or completeness theorem for CPEL;
- equivalence of unrestricted ST and LP consequence;
- classicality of every formula in every probability-integrity model;
- global classical consequence from local value recovery alone.

## Reproduce on Windows / PowerShell

```powershell
git fetch origin
git switch research/recovery-consequence-transfer-gate9
git pull --ff-only
lake build
lake env lean PEL4/RecoveryConsequenceTransferAxiomAudit.lean
python scripts/check_paper_axioms.py --report paper-axioms.json
python scripts/check_mpfg_axioms.py
python -m unittest discover -s scripts -p 'test_*.py'
python scripts/check_paper.py --check-committed
```

Current verified snapshot:

- full Lean build: 151 jobs;
- Gate 9 audit: 23 declarations;
- central manuscript audit: 157 declarations, all standard-allow-listed;
- MPFG audit: 24 declarations;
- script tests: six passing;
- manuscript: 54 pages, with the committed-text check enabled after commit.
