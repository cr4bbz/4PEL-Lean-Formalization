# Knowledge sanity gate before Fitch

Status: verified knowledge sanity, conjunction boundary, and conjunction introduction on `research/preface-case-study`. Raw possibility versus the internal knowledge dual is the next build gate.

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

`PEL4/KnowledgeConjunctionIntroduction.lean` is now also compiler-verified.
Lean verifies both underlying closure principles:

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

The conjunction behaviour is therefore genuinely directional:

```text
composition preserves epistemic stability,
decomposition need not reflect epistemic stability.
```

This is the current sharp structural diagnosis of the conjunction step relevant
to Fitch.

## New possibility-duality gate

Fitch also needs a possibility / knowability operator. The project should not
identify raw accessibility possibility with the internal dual

```text
not K(not phi)
```

without checking the four-valued semantics.

`PEL4/KnowledgePossibility.lean` therefore introduces two semantic candidates
without yet changing the object language.

Raw accessibility possibility:

```text
Diamond_raw+(phi) = some accessible world positively supports phi
Diamond_raw-(phi) = every accessible world negatively supports phi.
```

Internal knowledge dual:

```text
Diamond_K(phi) = FDE.not (K*(not phi)).
```

The key build candidates are:

1. FDE negation preserves accessible value stability;
2. if `phi` is unstable across the accessible range, then
   `Diamond_K(phi) = T`;
3. on homogeneous two-world profiles both notions recover the same full FDE
   value;
4. on a `B/F` profile raw possibility is `B` while the knowledge dual is `T`;
5. on an `N/F` profile raw possibility is `N` while the knowledge dual is `T`.

If these compile, the internal dual has a precise failure mode: evidence-stable
knowledge turns heterogeneity of `not phi` into `F`, and outer negation then
turns that failure into strict `T`. The dual can therefore erase glut/gap
structure that raw accessibility possibility still records.

## Why this matters for Fitch

The standard Fitch derivation combines:

```text
p and not K(p)
possibility / knowability
knowledge of a conjunction
conjunction elimination
factivity.
```

The current verified development already shows that the conjunction-elimination
step is licensed only under a component-stability condition. The new possibility
gate asks whether the modal possibility step also imports a hidden transport
assumption.

If raw possibility and `not K(not _)` diverge, a future 4-PEL Fitch
formalization should use an explicit accessibility-based possibility operator
and compare the internal dual only as a derived notion on fragments where an
equivalence theorem is available.

## Next sequence

After a successful possibility build:

1. characterize a fragment where raw possibility and the knowledge dual agree;
2. identify the corresponding classical / stable recovery conditions;
3. promote `K` and raw possibility to object-language syntax;
4. encode the Fitch derivation step by step, recording exactly which transports
   are theorems and which require extra assumptions.

The methodological question remains:

```text
Which Fitch steps are semantic theorems of evidence-stable four-valued
knowledge, and which are imported classical transport principles?
```
