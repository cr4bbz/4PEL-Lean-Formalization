# Knowledge semantics gate before Fitch

Status: literature-grounded design gate. No `K` operator has been added to the Lean object language yet.

## Why a gate is necessary

The current 4-PEL language contains probabilistic threshold belief `B`, internal FDE negation, and an explicit meta-level epistemic-status layer. The recent verified results show that

```text
internal not B(phi)
```

and

```text
absence of positive belief in phi
```

coincide exactly on the classical states `T` and `F`, but diverge on `B` and `N`.

A knowledge operator must therefore not be introduced by simply renaming `B` or by importing the ordinary modal `Box` without checking its four-valued semantics.

## Literature gate

### Standard FDE modal `Box`

Standard modal expansions of Belnap-Dunn / FDE use a `Box`-like operator whose positive condition is universal positive support over accessible worlds and whose negative condition is existential negative support over accessible worlds.

This is mathematically established modal-FDE machinery, but recent epistemic work argues that the ordinary `Box` is not always a good formalization of knowledge or belief in a Belnap-Dunn information setting.

Kozhemiachenko and Vashentseva, *Knowledge and ignorance in Belnap--Dunn logic* (2023/2024), explicitly argue that standard `Box` can treat a proposition as known even while its full Belnapian value varies across accessible states. They introduce a non-standard modality, written `blacksquare`, intended for knowledge/belief.

The key epistemic intuition is stronger than ordinary universal positive support:

```text
K(phi) should require phi to be positively supported throughout the accessible range
AND the Belnapian status of phi should be stable throughout that range.
```

On suitable S5-style frames their operator supports truthfulness and positive/negative introspection.

### Four-valued dynamic epistemic logic

Santos, *A Four-Valued Dynamic Epistemic Logic* (2020), also shows why negated modal formulas require care in a four-valued epistemic language. In that framework, a formula such as `not Box phi` need not mean simple absence of knowledge; it can instead have a possibility/evidence-against reading after normalization.

This independently reinforces the design constraint already proved inside 4-PEL:

```text
internal epistemic negation != meta-level epistemic absence
```

### Fitch and paraconsistent revision

The standard Fitch derivation uses an unknown truth of the form

```text
p and not K(p)
```

and then considers possible knowledge of that conjunction. The crucial reductio derives

```text
K(p) and not K(p).
```

The Stanford Encyclopedia survey of Fitch's paradox notes a paraconsistent line, associated especially with Beall, according to which the proof relies on treating such epistemic contradictions as impossible. If contradiction is non-explosive and epistemic gluts are possible, that reductio step becomes a substantive semantic assumption rather than an automatic endpoint.

This makes Fitch a particularly strong test for 4-PEL, but only after `K` and epistemic negation are kept distinct.

## Candidate architecture for 4-PEL knowledge

The current preferred design is to keep three levels separate.

### 1. Probabilistic belief `B`

Existing operator:

```text
B_i(phi) = independent thresholding of positive and negative probability mass.
```

This operator is non-factive and explicitly probabilistic.

### 2. Epistemic status predicates

Already verified:

```text
positivelyBelieves
negativelyBelieves
lacksPositiveBelief
lacksNegativeBelief
strictlyPositivelyBelieves
strictlyNegativelyBelieves
hasGluttyBelief
hasGappyBelief
```

These remain meta-level diagnostics and are not modal knowledge.

### 3. Distinct knowledge operator `K`

A future `K_i(phi)` should be evaluated independently of the Lockean threshold. The preferred first candidate is an evidence-stability semantics inspired by non-standard Belnap-Dunn epistemic modalities:

```text
positive K_i(phi) at w
iff
  phi is positively supported at every world accessible from w
  AND phi has the same complete FDE value at every accessible world.
```

The negative component must be specified separately rather than assumed to be Boolean complement. This is an open design choice and should be tested against factivity, conjunction behavior, introspection, and Fitch.

## Knowledge absence must remain separate

Even after `K` is introduced, the project should distinguish at least:

```text
internal not K(phi)
lacksPositiveKnowledge(phi)
negative knowledge-support for phi
ignorance / not knowing whether phi
```

The literature on Belnap-Dunn knowledge and ignorance supports treating these as genuinely different notions rather than syntactic variants.

## Modal possibility / knowability

Fitch also requires a possibility operator. The project should not define knowability simply as internal duality

```text
Diamond phi := not K(not phi)
```

until the semantics of internal negation around `K` is understood. In four-valued settings this dual can encode more than simple existential accessibility.

Preferred implementation sequence:

1. define a raw accessibility-based possibility operator independently;
2. compare it formally with the De-Morgan-style dual of `K`;
3. prove equivalence only under explicit conditions, if equivalence actually holds;
4. define knowability using the intended possibility notion rather than notation-first duality.

## Tests required before Fitch

Any proposed `K` should be checked for:

```text
Factivity:
  positive K(phi) -> positive phi at the actual world

Conjunction elimination:
  positive K(phi and psi) -> positive K(phi)
  positive K(phi and psi) -> positive K(psi)

Conjunction introduction / distribution:
  determine whether K(phi) and K(psi) imply K(phi and psi)

Classical recovery:
  on fully classical models, compare the operator with ordinary S5-style knowledge

Glut behavior:
  can K(phi) itself be B?

Gap behavior:
  can K(phi) itself be N?

Negation separation:
  compare internal not K(phi) with lacksPositiveKnowledge(phi)

Possibility duality:
  compare raw Diamond with not K(not phi)
```

Only after these tests should the actual Fitch derivation be encoded.

## Expected Fitch research question

The point is not merely to ask whether Fitch's derivation still goes through. The sharper structural-transport question is:

```text
Which preservation principle fails, or which additional impossibility assumption is required,
when knowability is transported through conjunction, knowledge, negation, and modal possibility?
```

In particular, 4-PEL should isolate whether the classical step

```text
K(p) and not K(p)  =>  impossible
```

is a theorem of the chosen knowledge semantics or an additional classicality condition.

## Current recommendation

Do not implement Fitch yet.

Next Lean gate:

1. introduce a small `KnowledgeSemantics.lean` module with a candidate evidence-stability operator;
2. keep its positive and negative conditions explicit;
3. prove the semantic sanity checks above on finite models;
4. compare standard FDE `Box`-style knowledge with evidence-stable `K` using countermodels;
5. only then introduce knowability and the Fitch construction.

This preserves the project's core methodological rule: theorem, model, interpretation, and philosophical identification must remain distinct layers.

## Literature anchors

- Daniil Kozhemiachenko and Liubov Vashentseva, *Knowledge and ignorance in Belnap--Dunn logic*, Journal of Logic and Computation / arXiv:2309.01449.
- Yuri David Santos, *A Four-Valued Dynamic Epistemic Logic*, Journal of Logic, Language and Information 29 (2020), 451--489.
- Stanford Encyclopedia of Philosophy, *Fitch's Paradox of Knowability*, especially the sections on the standard derivation and paraconsistent revision.
- Jc Beall, work on paraconsistent responses to the knowability paradox and possible epistemic oddities.
