# Gate 22: cumulative-scope stuttering

## Research question

Does every changed belief observation localized by Gate 21 consume a strict
unit of the cumulative evidence scope bounded by Gate 20?

## Answer

Not unconditionally at the same belief node. The exact verified answer is a
causal dichotomy:

```text
changed classicality status of B_i(body) at w
->
strict cumulative-scope shrinkage at (i,w)
or
body changed at an i-accessible world.
```

Thus a belief result can change without fresh local reweighting when its body
already changed deeper in the modal evaluation tree. This inherited-change
case is the precise reason why a pointwise identification of recovery flips
with local scope losses would be too strong.

## The missing concentration invariant

Gate 20's cumulative scope was initially a finite-list construction. To use it
probabilistically, Gate 22 introduces
`LocalMeasureConcentratedOn m i w scope`. It states that every well-formed
accessible event has the same mass as its intersection with `scope`.

Lean proves:

1. an integrity-respecting prior is concentrated on its full accessibility
   range;
2. conditionalization preserves concentration while intersecting the old
   scope with the new positive-evidence event;
3. consequently, the final posterior of every dependent finite update trace
   is concentrated on the final cumulative Gate-20 scope.

The last result upgrades the scope from bookkeeping to an actual posterior
support envelope. It does not claim that every world remaining in the envelope
has positive mass.

## Local stuttering theorem

If the next positive-evidence event contains the whole current concentration
scope, its probability is one and conditionalization preserves the mass of
every well-formed accessible event. Gate 20 expresses the same condition by
the absence of a strict length decrease.

If, in addition, the interpreted body value agrees at every accessible world,
Lean proves equality of the complete four-valued belief result. Both threshold
coordinates therefore stutter:

```text
no strict local scope loss
+ no accessible body-value change
-> complete belief value unchanged.
```

Taking the contrapositive yields the Gate-22 causal dichotomy above.

## Connection to the Gate-21 compiler

Gate 21 already proves that every recovery change on finite roots has a
changed compiled belief observation. Gate 22 refines that witness: at its
agent/world coordinate there is either a strict cumulative-scope loss or an
accessible body change. A trace-indexed theorem automatically chooses the
actual cumulative final scope of the preceding update prefix and obtains its
concentration proof from the trace.

## Gate-23 resolution

Gate 22 does not by itself turn the disjunction into a numerical global flip
bound. Gate 23 now chases inherited body changes recursively through belief,
knowledge, possibility, conjunction, and negation. Because the formula is
finite and atomic values cannot change, Lean proves termination at a reachable
belief node whose own scope shrinks strictly.

Gate 23 answered the causal question and Gate 24 has now completed the first
quantitative aggregation:

> Can repeated recovery-changing edges be charged to the finite budgets of
> reachable belief-observation positions?

Yes. Gate 24 sums over all positions; compiler duplicates safely loosen the
bound. Removing them is the sharper coordinate-quotient question proposed for
Gate 25.

## Verification

```powershell
lake build
lake env lean PEL4/RecoveryScopeStutteringAxiomAudit.lean
```
