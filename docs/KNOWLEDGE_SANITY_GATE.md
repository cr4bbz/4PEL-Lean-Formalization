# Knowledge sanity gate before Fitch

Status: verified knowledge sanity, conjunction transport, and raw-possibility versus internal-duality results on `research/preface-case-study`. The exact possibility-duality boundary is the next build gate.

## Verified knowledge semantics

The current `lake build` verifies the complete evidence-stable four-valued
knowledge candidate in `PEL4/KnowledgeSemantics.lean`.

```text
K*(phi) = (K+(phi), K-(phi))

K+(phi) = universal positive support AND stable complete FDE value
K-(phi) = accessible negative support OR unstable complete FDE value.
```

The verified finite semantics establishes:

```text
homogeneous T -> K*(phi) = T
homogeneous F -> K*(phi) = F
homogeneous B -> K*(phi) = B
homogeneous N -> K*(phi) = N
heterogeneous accessible FDE status -> K*(phi) = F.
```

Thus the knowledge candidate can itself be glutty or gappy. It is not a
Boolean-valued wrapper around FDE.

## Verified sanity results

### Reflexive factivity

Lean verifies:

```text
w in R_i(w)
and K+(phi) at w
implies phi+ at w.
```

### Internal negation versus absence of knowledge

Lean verifies:

```text
(FDE.not K*(phi)).pos = lacksPositiveKnowledge(phi)
    iff
K*(phi) is classical.
```

Hence internal negation and meta-level absence of positive knowledge diverge
exactly at the nonclassical knowledge values `B` and `N`.

## Verified conjunction transport

### Unrestricted conjunction elimination fails

The verified crossed witness is:

```text
left:   p = T, q = B
right:  p = B, q = T.
```

At both worlds `p and q = B`, so

```text
K*(p and q) = B
K*(p)       = F
K*(q)       = F.
```

Therefore positive knowledge of a conjunction does not in general transport to
positive knowledge of its conjuncts.

### Exact elimination boundary

`PEL4/KnowledgeConjunctionBoundary.lean` is compiler-verified. Assuming
`K+(phi and psi)`, positive support has already transported to each component.
The only remaining condition is component-level FDE stability:

```text
assuming K+(phi and psi):

K+(phi) iff Stable(phi)
K+(psi) iff Stable(psi).
```

The failure is therefore precisely a failure of stability reflection from a
stable compound to its components.

### Conjunction introduction

`PEL4/KnowledgeConjunctionIntroduction.lean` is compiler-verified. Lean verifies
both underlying closure principles:

```text
Box+(phi) and Box+(psi)
  -> Box+(phi and psi)

Stable(phi) and Stable(psi)
  -> Stable(phi and psi),
```

and hence the unrestricted positive knowledge rule:

```text
K+(phi) and K+(psi)
  -> K+(phi and psi).
```

The conjunction behaviour is genuinely directional:

```text
composition preserves epistemic stability,
decomposition need not reflect epistemic stability.
```

## Verified possibility-duality results

`PEL4/KnowledgePossibility.lean` is now compiler-verified.

Raw accessibility possibility is kept distinct from the internal De-Morgan
candidate:

```text
Diamond_raw+(phi) = some accessible world positively supports phi
Diamond_raw-(phi) = every accessible world negatively supports phi

Diamond_K(phi) = FDE.not (K*(not phi)).
```

Lean verifies:

```text
Stable(not phi) = Stable(phi).
```

It also verifies the key instability collapse:

```text
not Stable(phi)
  -> Diamond_K(phi) = T.
```

Hence the internal knowledge dual treats accessible FDE-value heterogeneity very
differently from raw accessibility possibility.

The finite witnesses are verified:

```text
accessible B/F profile:
  Diamond_raw(phi) = B
  Diamond_K(phi)   = T

accessible N/F profile:
  Diamond_raw(phi) = N
  Diamond_K(phi)   = T.
```

On homogeneous two-world profiles both operators recover the same underlying
FDE value `T`, `F`, `B`, or `N`.

Thus the classical-looking abbreviation

```text
Diamond phi := not K(not phi)
```

is not globally semantics-preserving for the evidence-stable knowledge
candidate. It can erase glut/gap structure by turning instability into strict
truth.

## New exact possibility-duality boundary gate

`PEL4/KnowledgePossibilityBoundary.lean` sharpens the previous result.

The internal dual has the target component form:

```text
Diamond_K+(phi)
  = not Stable(phi) OR Diamond_raw+(phi)

Diamond_K-(phi)
  = Diamond_raw-(phi) AND Stable(phi).
```

This predicts two regimes.

### Stable regime

```text
Stable(phi)
  -> Diamond_raw(phi) = Diamond_K(phi).
```

Here the classical-looking duality is genuinely recovered.

### Unstable regime

```text
not Stable(phi)
  -> Diamond_K(phi) = T.
```

Therefore equality can survive instability only when raw possibility is already
strict `T`.

The exact target theorem is:

```text
Diamond_raw(phi) = Diamond_K(phi)
iff
Stable(phi) OR Diamond_raw(phi) = T.
```

The second disjunct is important. An unstable `T/F` profile has

```text
Diamond_raw(phi) = T
Diamond_K(phi)   = T,
```

so equality holds extensionally even though it is not stability-based modal
duality. The boundary theorem therefore distinguishes genuine stable recovery
from accidental agreement after the dual's instability collapse.

## Why this matters for Fitch

The standard Fitch derivation combines:

```text
p and not K(p)
possibility / knowability
knowledge of a conjunction
conjunction elimination
factivity.
```

The verified development now identifies two independent structural pressure
points:

1. knowledge of a conjunction does not generally decompose without
   component-level stability;
2. raw possibility does not generally equal `not K(not _)` outside the stable
   fragment.

A future 4-PEL Fitch formalization should therefore use explicit raw
accessibility possibility and explicit evidence-stable knowledge. Any use of
conjunction elimination or modal duality should be justified by a theorem or
stated as an additional transport principle.

## Next sequence

After a successful `KnowledgePossibilityBoundary.lean` build:

1. promote evidence-stable `K` and raw possibility to object-language syntax;
2. encode the Fitch derivation step by step;
3. record for each classical proof move whether it is a theorem of the chosen
   semantics, valid only on a stable/reflexive fragment, or an extra assumption;
4. isolate the minimal package of transport principles needed to recover the
   classical paradox.

The methodological question remains:

```text
Which Fitch steps are semantic theorems of evidence-stable four-valued
knowledge, and which are imported classical transport principles?
```
