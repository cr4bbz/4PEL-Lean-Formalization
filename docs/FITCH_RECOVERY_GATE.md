# Fitch recovery boundary

Status: `PEL4/Paradoxes/Fitch.lean` is compiler-verified on `research/preface-case-study`. `PEL4/Paradoxes/FitchRecovery.lean` is the current build gate.

## Verified object-language Fitch fracture

The conservative modal language now contains primitive evidence-stable `K` and primitive raw accessibility `Diamond`.

Lean verifies a concrete Fitch-shaped model with

```text
M(p) := p and not K(p)
```

such that at the actual state

```text
M(p) = T
Diamond_raw K(M(p)) = B,
```

while at a reflexive possible witness

```text
M(p)        = B
K(M(p))     = B
K(p)        = F
K(not K(p)) = F.
```

Hence positive knowledge of the Moorean conjunction does not transport to positive knowledge of either component, even at a reflexive critical point.

The verified structural reason is

```text
Stable(M(p))     = true
Stable(p)        = false
Stable(not K(p)) = false.
```

The classical contradiction-shaped formula `K(p) and not K(p)` is `F` at that witness.

## Current recovery gate

The new module asks which additional assumptions restore the local classical Fitch collision.

It first lifts the previously verified conjunction boundary to arbitrary formulas of the modal object language:

```text
assuming K+(phi and psi):

K+(phi) iff Stable(phi).
```

It also proves modal reflexive factivity:

```text
w in R_i(w)
and K+(phi) at w
implies phi+ at w.
```

Define local non-gluttiness of knowledge by

```text
NoGlut(K phi):
  K+(phi) -> not K-(phi).
```

The target local Fitch theorem is then

```text
K+(phi and not K(phi))
+ Stable(phi)
+ reflexivity at w
+ NoGlut(K phi)
--------------------------------
False.
```

Only the left component has to be extracted. Reflexive factivity of knowledge of the compound already yields `not K(phi)` at the critical point.

Thus the candidate minimal local recovery package is

```text
reflexivity
+ component stability
+ knowledge no-glut.
```

The existing verified countermodel is designed to satisfy reflexivity and local no-glut while violating exactly component stability. If the new build succeeds, this isolates the missing Fitch transport condition very sharply.

## Next gate

After local recovery is verified, lift the result through primitive raw possibility. The global theorem should make explicit which frame/stability/no-glut conditions are required at every possible knowledge witness before a knowability premise can reproduce the classical Fitch collapse.
