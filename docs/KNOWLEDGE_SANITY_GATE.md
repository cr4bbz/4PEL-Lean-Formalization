# Knowledge sanity gate before Fitch

Status: verified sanity gate; conjunction-boundary characterization is the next build gate on `research/preface-case-study`.

## Verified input

The current `lake build` verifies the complete evidence-stable four-valued
knowledge candidate in `PEL4/KnowledgeSemantics.lean` and the sanity checks in
`PEL4/KnowledgeSanity.lean`.

Its semantic value is

```text
K*(phi) = (K+(phi), K-(phi))
```

with

```text
K+(phi) = universal positive support AND stable complete FDE value
K-(phi) = accessible negative support OR unstable complete FDE value.
```

The verified finite gate establishes:

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

### 1. Reflexive factivity

Lean verifies:

```text
w in R_i(w)
and K+(phi) at w
implies phi+ at w.
```

This is the positive four-valued form of factivity. It requires reflexivity at
the actual point rather than being built into the generic `Model` structure.

### 2. Internal negation versus absence of knowledge

Define

```text
lacksPositiveKnowledge(phi) = not K+(phi)
```

at the meta level, and compare it with the positive bit of internal FDE
negation of the full knowledge value.

Lean verifies

```text
(FDE.not K*(phi)).pos = lacksPositiveKnowledge(phi)
    iff
K*(phi) is classical.
```

Hence the same separation already proved for threshold belief reappears at the
knowledge level. If `K*(phi)` is `B` or `N`, internal negation and absence of
positive knowledge diverge.

### 3. Unrestricted conjunction elimination fails

The verified finite witness uses two accessible worlds:

```text
left:   p = T, q = B
right:  p = B, q = T.
```

At both worlds,

```text
p and q = B.
```

Therefore

```text
K*(p and q) = B,
```

while the individual conjuncts are unstable and hence

```text
K*(p) = F
K*(q) = F.
```

Lean verifies the positive transport failure:

```text
K+(p and q) = true
K+(p)       = false
K+(q)       = false.
```

This isolates a structural transport failure:

```text
positive knowledge of conjunction
  -/->
positive knowledge of conjunct.
```

## New conjunction-boundary gate

The countermodel suggests a sharper result than simple non-distributivity.
`K+(phi and psi)` already guarantees universal positive support for both
conjuncts. What can fail is only the stability requirement of the individual
conjunct.

`PEL4/KnowledgeConjunctionBoundary.lean` therefore targets the exact local
characterization:

```text
assuming K+(phi and psi):

K+(phi) iff Stable(phi)
K+(psi) iff Stable(psi).
```

Equivalently, conjunction elimination is restored as soon as the target
conjunct has a stable full FDE value across the accessible range.

The existing crossed `T/B` countermodel should sit exactly on the failure side:

```text
Stable(p and q) = true
Stable(p)       = false
Stable(q)       = false.
```

If this builds, the knowledge/conjunction failure receives an exact structural
boundary: the conjunction can mask component-level information instability.

## Why this matters for Fitch

The standard Fitch derivation considers possible knowledge of a conjunction of
the form

```text
p and not K(p)
```

and then uses knowledge/conjunction principles to extract epistemic claims about
its conjuncts. Under evidence-stable four-valued knowledge, that extraction is
not automatic.

The sharper question is now:

```text
Does the relevant Fitch conjunction satisfy the component-stability condition
needed for conjunction elimination?
```

If yes, the classical step may be recovered locally. If not, Fitch relies on a
transport principle that the semantics rejects.

This does not by itself refute or solve Fitch. It identifies an exact semantic
condition under which one of the standard proof moves is licensed.

## Literature alignment

Kozhemiachenko and Vashentseva explicitly note that their non-standard
Belnap-Dunn knowledge modality is non-compositional with respect to conjunction
in the presence of paradoxical values. They show that unrestricted
conjunction-elimination behaviour requires additional frame restrictions and
explain the failure through variation of full Belnapian values across accessible
states.

The present 4-PEL development therefore treats the finite countermodel as an
implementation-level realization of an established semantic phenomenon, while
the new contribution of the current gate is to characterize the exact local
stability condition inside this implementation.

## Next gate after a successful build

If `KnowledgeConjunctionBoundary.lean` compiles, the next sequence is:

1. test conjunction introduction separately;
2. compare raw accessibility possibility with the internal dual of knowledge;
3. characterize classical fragments / frame conditions where normal modal
   behaviour is recovered;
4. only then add object-language `K` / possibility syntax and encode Fitch.

The key methodological question remains:

```text
Which Fitch steps are semantic theorems of evidence-stable four-valued
knowledge, and which require extra classical or modal transport principles?
```
