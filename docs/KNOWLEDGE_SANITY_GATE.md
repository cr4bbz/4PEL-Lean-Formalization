# Knowledge sanity gate before Fitch

Status: all semantic knowledge/conjunction/possibility gates below are compiler-verified on `research/preface-case-study`. `PEL4/ModalLanguage.lean` is the next build gate.

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

The failure is precisely a failure of stability reflection from a stable
compound to its components.

### Conjunction introduction

`PEL4/KnowledgeConjunctionIntroduction.lean` is compiler-verified. Lean verifies
both underlying closure principles:

```text
Box+(phi) and Box+(psi)
  -> Box+(phi and psi)

Stable(phi) and Stable(psi)
  -> Stable(phi and psi),
```

and hence:

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

`PEL4/KnowledgePossibility.lean` and
`PEL4/KnowledgePossibilityBoundary.lean` are compiler-verified.

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

and the key instability collapse:

```text
not Stable(phi)
  -> Diamond_K(phi) = T.
```

Finite divergence witnesses are verified:

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

### Exact possibility-duality boundary

Lean now verifies the component form:

```text
Diamond_K+(phi)
  = not Stable(phi) OR Diamond_raw+(phi)

Diamond_K-(phi)
  = Diamond_raw-(phi) AND Stable(phi).
```

Therefore:

```text
Diamond_raw(phi) = Diamond_K(phi)
iff
Stable(phi) OR Diamond_raw(phi) = T.
```

This separates two qualitatively different forms of agreement.

```text
Stable(phi):
  genuine structural recovery of the classical-looking duality.

not Stable(phi) and Diamond_raw(phi) = T:
  accidental extensional agreement after the internal dual collapses to T.
```

An unstable `T/F` profile witnesses the second case.

## Why this matters for Fitch

The standard Fitch derivation combines:

```text
p and not K(p)
possibility / knowability
knowledge of a conjunction
conjunction elimination
factivity.
```

The verified development identifies two independent structural pressure points:

1. knowledge of a conjunction does not generally decompose without
   component-level stability;
2. raw possibility does not generally equal `not K(not _)` outside the stable
   fragment.

A 4-PEL Fitch formalization should therefore use explicit raw accessibility
possibility and explicit evidence-stable knowledge. Any use of conjunction
elimination or modal duality must be justified by a theorem or stated as an
additional transport principle.

## Current object-language gate

`PEL4/ModalLanguage.lean` adds a conservative modal object language rather than
mutating the already verified legacy `Formula` type across the entire project.

The new syntax is:

```text
ModalFormula ::= p | not phi | phi and psi | B_i(phi) | K_i(phi) | Diamond_i(phi)
```

where:

```text
K_i(phi)
  = primitive evidence-stable four-valued knowledge

Diamond_i(phi)
  = primitive raw accessibility possibility.
```

The internal expression

```text
not K_i(not phi)
```

remains syntactically and semantically distinct from primitive `Diamond_i(phi)`.

The build candidates are:

1. every legacy `Formula` embeds into `ModalFormula` without changing its value;
2. primitive modal `K` on embedded formulas reproduces
   `evidenceStableKnowledgeValue`;
3. primitive modal `Diamond` on embedded formulas reproduces
   `rawPossibilityValue`;
4. the previous `B/F` possibility-divergence witness is expressible entirely
   inside the modal object language.

This conservative layer avoids mixing the Fitch experiment with a repository-wide
syntax refactor. If the gate compiles, Fitch can be encoded directly in this
language while all existing results remain untouched.

## Next sequence

After a successful `ModalLanguage.lean` build:

1. encode the Fitch sentence `p and not K(p)` in the modal object language;
2. encode raw knowability using primitive `Diamond`;
3. formalize the classical Fitch proof moves one by one;
4. mark each move as a semantic theorem, a stable/reflexive-fragment theorem,
   or an additional transport assumption;
5. isolate the minimal package that restores the classical paradox.

The methodological question is now ready to be asked inside one object language:

```text
Which Fitch steps are theorems of evidence-stable four-valued knowledge,
and which are imported classical transport principles?
```
