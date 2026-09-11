# Paper review after Gate 24

## Review target

This review compares manuscript version 0.13 with the formal development now
completed through Gate 24. It reviews theorem currency and claim scope; it is
not an external literature or novelty review.

## Overall judgment

Gate 24 closes the numerical gap left by Gate 23. The formal development now
contains a trace-length-independent upper bound on recovery-status changes in
finite admissible conditionalization traces. The manuscript does not yet
contain Gates 20--24 and must not be described as current for this result.

## Findings by priority

### High: state the strengthened invariant

The paper should lead with the proved resource inequality

```text
changes + final remaining potential <= initial potential,
```

then derive the simpler change-count bound. Presenting only the corollary would
hide the inductive invariant that makes the finite accounting work.

### High: distinguish positions from coordinates

The current potential sums over compiled belief-observation positions. It does
not quotient repeated occurrences with the same agent/world coordinate. This
is a safe but potentially loose bound, not a duplicate-free optimum. The
Gate-19 computation `2 + 4 <= 16` should be used to make that distinction
concrete.

### High: retain the coverage and update-class guards

The executable status is exactly recovery on the chosen finite roots. A global
interpretation requires `WorldListCovers`. The theorem concerns finite
dependent traces of admissible conditionalizations and should not be generalized
in prose to product updates, arbitrary transformations, or infinite traces.

### Medium: separate status changes from value changes

The count records edges on which the Boolean compositional-recovery predicate
changes. It does not count every change of an FDE value, every threshold-wall
crossing, or every local scope shrinkage. Multiple local losses may pay for one
status change.

### Medium: preserve the Gate-20--24 dependency chain

The manuscript should present the result as the endpoint of one argument:

```text
finite local scope descent
-> exact finite observation compiler
-> posterior concentration and stuttering
-> recursive causal localization
-> finite trace-level recovery-flip budget.
```

Removing the intermediate gates would obscure why inherited modal body changes
cannot evade the finite resource measure.

## Axiom and verification status

The focused Gate-24 audit covers fourteen declarations. Their dependencies stay
within the repository allow-list `propext`, `Classical.choice`, and
`Quot.sound`. No audited Gate-24 result depends on a project-specific axiom or
a native-decision axiom.

## Layout status

Gate 24 changes no TeX source. The committed manuscript remains version 0.13
and 54 pages, so no new PDF render is warranted on this branch. A future
version-0.14 integration should include Gates 20--24 as a unit and then receive
a full render and visual review.

## Editorial decision

Gate 24 is ready for later manuscript integration as a finite position-wise
resource theorem. A duplicate-free coordinate bound remains a distinct Gate-25
claim and must not be presented as already proved.
