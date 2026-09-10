# Paper review after Gate 20

## Review target

This review compares manuscript version 0.13 with the formal development now
completed through Gate 20. It is a currency and claim-scope review, not an
independent external peer review.

## Overall judgment

Gate 20 strengthens the finite-update research program without invalidating a
manuscript claim. It also sharpens a necessary editorial boundary: a finite
local evidence budget is not yet a theorem bounding global recovery flips.
The manuscript remains substantially behind the Lean development because its
main theorem narrative still ends at Gate 9.

## Findings by priority

### High: distinguish local scope shrinkage from recovery change

The verified theorem concerns one fixed agent/world site. It counts strict
decreases of a cumulative intersection of positive evidence extensions. The
paper must not rewrite this as “recovery changes at most `n` times” for a model
or formula. Such a statement still needs a finite enumeration of all
formula-reachable belief sites and a stuttering theorem connecting unchanged
local data to unchanged recovery.

### High: state the stronger resource inequality

The useful result is not merely finiteness. Gate 20 proves

```text
remaining local scope size + strict local shrink count
<= initial local scope size.
```

This exposes the resource interpretation: each strict event spends at least
one initially available world. The three-world witness shows the bound can be
attained.

### Medium: use Gate 19 only as an illustration

In the Gate-19 loss-and-return witness, two recovery changes coincide with two
strict local scope shrinkages. This checked computation is a good running
example, but it supplies no converse or formula-independent law. The prose
should label it as an instance, not evidence for a proved equivalence.

### Medium: preserve the dependent-trace qualification

Later evidence extensions are evaluated in the posterior source models that
earlier updates produce. The Gate-20 compiler preserves this dependency; a
plain precomputed list of static evidence sets would misdescribe the theorem.

## Recommended manuscript placement

Add Gate 20 immediately after the Gate-19 finite-trace section as a short
“local resource bound and open global bridge” subsection. The manuscript
should then state the reachable-site compiler and stuttering lemma as future
work. No completeness, decidability, product-update, infinite-trace, or global
flip-bound claim is warranted.

## Layout status

Gate 20 changes no TeX source. The committed manuscript remains version 0.13
and 54 pages. A later integration should be a deliberate versioned manuscript
revision with a fresh render and visual review.

## Editorial decision

Gate 20 is suitable for integration as a precise partial answer: it proves a
sharp theorem, demonstrates it computationally, and identifies the exact
missing bridge to the stronger research claim. Its negative boundary is part
of the result and should remain visible in the paper.
