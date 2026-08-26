# Knowledge sanity gate before Fitch

Status: historical gate, now passed. The semantic knowledge/conjunction/possibility layers, conservative modal object language, and Fitch modules are root-imported and compiler-verified on `research/complex-coordinates`.

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

Lean verifies:

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

This separates genuine stable recovery from accidental extensional agreement
under instability.

## Verified modal object language

`PEL4/ModalLanguage.lean` is compiler-verified. The legacy `Formula` language is
left unchanged and embeds conservatively into a modal extension:

```text
ModalFormula ::= p | not phi | phi and psi | B_i(phi) | K_i(phi) | Diamond_i(phi)
```

where primitive `K` uses evidence-stable four-valued knowledge and primitive
`Diamond` uses raw accessibility possibility.

Lean verifies the conservative bridge:

```text
evalModal(embed(phi)) = eval(phi).
```

It also verifies that modal `K` and modal raw `Diamond` reproduce the previously
analyzed semantic operators on every embedded legacy formula. The internal
expression

```text
not K_i(not phi)
```

remains syntactically and semantically distinct from primitive `Diamond_i(phi)`.

## Current object-language Fitch gate

`PEL4/Paradoxes/Fitch.lean` now encodes the Moorean Fitch sentence directly:

```text
M(p) = p and not K(p).
```

The finite model is designed to test the classical extraction step from

```text
K(M(p))
```

to

```text
K(p)
and
K(not K(p)).
```

The critical possible `witness` world is reflexive. The candidate profile is:

```text
at the actual world:
  M(p) = T
  Diamond_raw K(M(p)) = B

at the reflexive witness:
  M(p)       = B
  K(M(p))    = B
  K(p)       = F
  K(not K(p)) = F.
```

The intended structural witness is:

```text
Stable(M(p))       = true
Stable(p)          = false
Stable(not K(p))   = false.
```

If the build succeeds, this will be the first fully object-language Fitch
fracture result: positive knowledge of the Moorean conjunction is present, but
positive knowledge of either component cannot be extracted even at a reflexive
point. The classical contradiction-shaped formula `K(p) and not K(p)` should
remain `F` rather than becoming a glut.

This is not yet a general anti-Fitch theorem. It is a concrete model showing
that unrestricted knowledge-conjunction elimination is not available in the
actual Fitch-shaped formula under the chosen semantics.

## Next sequence

After a successful `PEL4/Paradoxes/Fitch.lean` build:

1. characterize the exact extra conditions that restore extraction from
   `K(p and not K(p))`;
2. distinguish positive/designated Fitch premises from strict-`T` premises;
3. formulate the minimal transport package needed for the classical collapse;
4. prove either a restricted Fitch theorem under that package or a general
   non-collapse result when one of the required transports is absent.

The central question is now fully object-linguistic:

```text
Which Fitch steps are theorems of evidence-stable four-valued knowledge,
and which are imported classical transport principles?
```
