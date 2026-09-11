# Paper review after Gate 23

## Review target

This review compares manuscript version 0.13 with the formal development now
completed through Gate 23. It is a currency and claim-scope review, not an
independent external peer review.

## Overall judgment

Gate 23 closes the qualitative causal gap left by Gate 22. Every recovery
change under one admissible conditionalization can now be localized to strict
cumulative-scope shrinkage at a belief observation reachable in the finite
Gate-21 compiler. The manuscript remains substantially behind this theorem
sequence and should not state the forthcoming numerical bound as completed.

## Findings by priority

### High: distinguish causal localization from numerical injection

Gate 23 proves existence of at least one strictly shrinking reachable belief
coordinate for every recovery-changing edge. It does not yet aggregate these
witnesses across a trace. Duplicate positions do not invalidate a sum bound,
but they can count the same coordinate budget more than once and make it less
sharp.

### High: present the Gate-22 disjunction as an intermediate lemma

The inherited-body-change alternative from Gate 22 is not a counterexample to
finite resource accounting. Gate 23 recursively follows that alternative and
proves that it terminates at a deeper belief node with strict local shrinkage.
The two gates should therefore be presented together.

### High: retain all scope guards

The result assumes probability integrity, admissible conditionalization, and
local concentration on the supplied cumulative scopes. For actual finite
update prefixes, concentration is derived rather than postulated. Global
recovery still requires a finite world-coverage proof.

### Medium: explain compiler duplicates before stating counts

The causal witness belongs to the original finite compiler, but compiler
positions are not quotient coordinates. The first numerical theorem may sum
over positions as a safe over-approximation; a later quotient by agent/world
coordinate can improve the bound.

## Recommended manuscript placement

Present Gates 20--23 as one argument:

```text
local finite scope budget
-> finite recovery-observation compiler
-> posterior concentration and local stuttering
-> recursive causal descent
-> strict shrinking belief witness for every recovery-changing edge
-> open position-wise trace bound and optional duplicate-free sharpening.
```

## Layout status

Gate 23 changes no TeX source. The committed manuscript remains version 0.13
and 54 pages. A future version-0.14 integration should include the entire
finite-update sequence and undergo a fresh render and visual review.

## Editorial decision

Gate 23 is suitable for manuscript integration as a qualitative localization
theorem. A numerical global recovery-flip bound must wait for Gate 24's
trace-level counting result; coordinate deduplication can be a later
sharpening.
