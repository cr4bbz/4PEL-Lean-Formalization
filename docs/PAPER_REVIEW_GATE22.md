# Paper review after Gate 22

## Review target

This review compares manuscript version 0.13 with the formal development now
completed through Gate 22. It is a currency and claim-scope review, not an
independent external peer review.

## Overall judgment

Gate 22 supplies the probabilistic concentration invariant missing between the
Gate-20 scope budget and the Gate-21 recovery compiler. It also corrects the
strongest anticipated claim: a changed belief observation need not itself
consume a fresh local scope unit, because its interpreted body may have
changed at a deeper reachable node.

## Findings by priority

### High: state the causal dichotomy, not a pointwise equivalence

The verified theorem is:

```text
changed belief classicality
-> strict local cumulative-scope loss OR accessible body change.
```

The manuscript must not simplify this to “every changed belief result spends
one local scope unit.” The inherited-change disjunct is mathematically real and
determines the next proof obligation.

### High: explain why cumulative scope is probabilistically meaningful

Gate 22 proves that each posterior measure is concentrated on the cumulative
scope produced by the preceding trace. The scope is a support envelope and
need not be the minimal support. This concentration theorem should be
presented before the stuttering result; otherwise the combinatorial Gate-20
scope appears disconnected from the probability measure used by belief.

### High: retain the finite-root and coverage guard

The Gate-21 localization used by Gate 22 remains a finite-root theorem. Global
recovery claims still require `WorldListCovers`. Gate 22 does not remove this
condition.

### Medium: distinguish value stuttering from status stuttering

The local result proves equality of the complete FDE belief value, which is
stronger than preservation of its classical/nonclassical status. The recovery
bridge consumes only the weaker status consequence.

## Recommended manuscript placement

Extend the finite-update section in this order:

```text
Gate-20 local scope budget
-> Gate-21 finite observation compiler
-> posterior concentration on cumulative scope
-> local complete-value stuttering
-> strict-shrink-or-inherited-change dichotomy
-> open recursive causal-descent and aggregation theorem.
```

## Layout status

Gate 22 changes no TeX source. The committed manuscript remains version 0.13
and 54 pages. Gates 19--22 should be integrated together in a deliberate
version-0.14 revision, followed by a fresh render and visual review.

## Editorial decision

Gate 22 is suitable for manuscript integration. Its main scientific value is
both positive and corrective: cumulative scope is now a proved posterior
support envelope, while the formal disjunction prevents an unjustified
one-change/one-local-loss slogan. Gate 23 should establish recursive causal
descent before the paper claims a global finite recovery-flip bound.
