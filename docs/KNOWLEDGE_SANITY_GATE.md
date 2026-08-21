# Knowledge sanity gate before Fitch

Status: verified sanity and conjunction-boundary results; conjunction introduction is the next build gate on `research/preface-case-study`.

## Verified input

The current `lake build` verifies the complete evidence-stable four-valued
knowledge candidate in `PEL4/KnowledgeSemantics.lean`, the sanity checks in
`PEL4/KnowledgeSanity.lean`, and the exact conjunction-elimination boundary in
`PEL4/KnowledgeConjunctionBoundary.lean`.

Its semantic value is

```text
K*(phi) = (K+(phi), K-(phi))
```

with

```text
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

Lean verifies

```text
(FDE.not K*(phi)).pos = lacksPositiveKnowledge(phi)
    iff
K*(phi) is classical.
```

Hence internal negation and meta-level absence of positive knowledge diverge
exactly at the nonclassical knowledge values `B` and `N`.

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

Lean verifies:

```text
K+(p and q) = true
K+(p)       = false
K+(q)       = false.
```

## Verified conjunction-elimination boundary

The stronger result is now compiler-verified. Assuming positive knowledge of a
conjunction, the positive-support part already transports to each conjunct.
The only remaining requirement is component-level FDE stability:

```text
assuming K+(phi and psi):

K+(phi) iff Stable(phi)
K+(psi) iff Stable(psi).
```

Hence conjunction elimination fails exactly when a stable compound masks an
unstable component. The crossed `T/B` witness sits precisely on that boundary:

```text
Stable(p and q) = true
Stable(p)       = false
Stable(q)       = false.
```

This is a structural-transport boundary theorem rather than merely a
counterexample to modal distribution.

## New conjunction-introduction gate

`PEL4/KnowledgeConjunctionIntroduction.lean` tests the reverse transport
direction. The candidate proof decomposes the result into two closure facts:

```text
Box+(phi) and Box+(psi)
  -> Box+(phi and psi)

Stable(phi) and Stable(psi)
  -> Stable(phi and psi).
```

Together these should yield the unrestricted positive knowledge rule

```text
K+(phi) and K+(psi)
  -> K+(phi and psi).
```

If the build succeeds, the conjunction behaviour is directionally asymmetric:

```text
composition preserves epistemic stability,
decomposition need not reflect epistemic stability.
```

The existing crossed `T/B` model is included as a witness to this asymmetry:
conjunction introduction is a general theorem, while conjunction elimination
fails in that concrete model.

## Why this matters for Fitch

The standard Fitch derivation considers possible knowledge of a conjunction of
the form

```text
p and not K(p)
```

and then extracts epistemic claims about its conjuncts. The verified boundary
shows that this eliminative step needs component stability under the present
knowledge semantics.

Conjunction introduction appears to behave differently: if both components are
already positively known, their stability composes forward. Thus the likely
Fitch pressure point is specifically decomposition of knowledge, not formation
of knowledge from already stable known components.

This does not yet settle Fitch. It identifies which direction of the
knowledge/conjunction transport is structurally fragile.

## Literature alignment

Kozhemiachenko and Vashentseva explicitly note that their non-standard
Belnap-Dunn knowledge modality is non-compositional with respect to conjunction
in the presence of paradoxical values. They show that unrestricted
conjunction-elimination behaviour requires additional frame restrictions and
explain the failure through variation of full Belnapian values across accessible
states.

The current 4-PEL development should therefore be read as a machine-checked
implementation and local structural analysis of that phenomenon, not as a
claim that the general non-compositionality itself is novel.

## Next gate after a successful build

If `KnowledgeConjunctionIntroduction.lean` compiles, the next sequence is:

1. compare raw accessibility possibility with the internal dual of knowledge;
2. characterize classical fragments / frame conditions where normal modal
   behaviour is recovered;
3. only then add object-language `K` / possibility syntax and encode Fitch.

The key methodological question remains:

```text
Which Fitch steps are semantic theorems of evidence-stable four-valued
knowledge, and which require extra classical or modal transport principles?
```
