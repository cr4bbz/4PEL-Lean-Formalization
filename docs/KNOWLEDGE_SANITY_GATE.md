# Knowledge sanity gate before Fitch

Status: build candidate on `research/preface-case-study`.

## Verified input

The previous `lake build` verifies the complete evidence-stable four-valued
knowledge candidate in `PEL4/KnowledgeSemantics.lean`.

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

## Current sanity gate

`PEL4/KnowledgeSanity.lean` now tests three properties before the semantics is
promoted to a primitive object-language operator.

### 1. Reflexive factivity

Candidate theorem:

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

The candidate theorem is

```text
(FDE.not K*(phi)).pos = lacksPositiveKnowledge(phi)
    iff
K*(phi) is classical.
```

Hence the same separation already proved for threshold belief is expected to
reappear at the knowledge level. If `K*(phi)` is `B` or `N`, internal negation
and absence of positive knowledge diverge.

### 3. Conjunction elimination

The literature-motivated non-standard Belnap-Dunn knowledge modality is not a
normal compositional modal operator. In particular, knowledge of a conjunction
need not entail knowledge of each conjunct on arbitrary frames.

The finite 4-PEL witness uses two accessible worlds:

```text
left:   p = T, q = B
right:  p = B, q = T.
```

At both worlds,

```text
p and q = B.
```

Therefore the conjunction has a stable complete FDE value and the candidate
predicts

```text
K*(p and q) = B.
```

But each conjunct separately varies between `T` and `B`, so the candidate
predicts

```text
K*(p) = F
K*(q) = F.
```

The target result is therefore

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

## Why this matters for Fitch

The standard Fitch derivation considers possible knowledge of a conjunction of
the form

```text
p and not K(p)
```

and then uses knowledge/conjunction principles to extract epistemic claims about
its conjuncts. If the selected four-valued knowledge operator does not validate
unrestricted conjunction elimination, that step must be stated as an explicit
additional principle rather than silently inherited from normal modal logic.

This does not by itself refute or solve Fitch. It identifies the first exact
transport principle that the four-valued semantics places under pressure.

## Literature alignment

Kozhemiachenko and Vashentseva explicitly note that their non-standard
Belnap-Dunn knowledge modality is non-compositional with respect to conjunction
in the presence of paradoxical values. They show that the unrestricted
conjunction-elimination pattern is valid only on partial-functional frames and
explain that the source of failure is precisely the requirement that the full
Belnapian value remain the same across accessible states.

This means the 4-PEL countermodel is intended as an implementation-level
realization of an established semantic phenomenon, not as a novelty claim.

## Next gate after a successful build

If the current sanity module compiles, the next decision is architectural:

1. characterize conditions under which conjunction elimination is restored;
2. test conjunction introduction separately;
3. compare raw accessibility possibility with the internal dual of knowledge;
4. only then add object-language `K` / possibility syntax and encode Fitch.

The key methodological question becomes:

```text
Which Fitch steps are semantic theorems of evidence-stable four-valued
knowledge, and which require extra classical or modal transport principles?
```
