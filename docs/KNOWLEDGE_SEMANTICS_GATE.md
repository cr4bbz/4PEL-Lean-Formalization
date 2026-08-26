# Knowledge semantics gate before Fitch

Status: historical gate, now passed. Full four-valued evidence-stable knowledge semantics and the modal object-language knowledge layer are root-imported and compiler-verified on `research/complex-coordinates`.

## Why a gate is necessary

The current 4-PEL language contains probabilistic threshold belief `B`, internal FDE negation, and an explicit meta-level epistemic-status layer. Lean verifies that

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

Kozhemiachenko and Vashentseva, *Knowledge and ignorance in Belnap--Dunn logic*, argue that the ordinary `Box` is not always a good formalization of knowledge or belief in a Belnap-Dunn information setting. In particular, `Box phi` may be positively supported while the complete Belnapian value of `phi` varies across accessible states.

They motivate a non-standard modality `blacksquare` whose positive support requires both:

```text
phi is positively supported at every accessible state
AND
phi has the same complete Belnapian value at every accessible state.
```

Their semantic analysis also shows that falsity of this knowledge modality is sensitive not merely to explicit negative support but to instability of the Belnapian value itself. In particular, accessible states with different non-false values can still refute knowledge.

This motivates the current 4-PEL candidate:

```text
K+.pos := universal positive support AND FDE-value stability
K-.neg := accessible negative support OR FDE-value instability.
```

On suitable S5-style frames the literature modality supports truthfulness and positive/negative introspection. It also behaves classically when all formulas have classical values throughout the model.

### Four-valued dynamic epistemic logic

Santos, *A Four-Valued Dynamic Epistemic Logic* (2020), independently shows why negated modal formulas require care in a four-valued epistemic language. The modal layer concerns agents' knowledge about potentially incomplete or conflicting evidence, and internal negation cannot automatically be read as simple absence of knowledge.

This reinforces the design constraint already proved inside 4-PEL:

```text
internal epistemic negation != meta-level epistemic absence.
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

The Stanford Encyclopedia survey notes the paraconsistent line associated especially with Beall: the proof relies on treating epistemic contradictions of this sort as impossible. If contradiction is non-explosive and epistemic gluts are possible, that impossibility becomes a substantive semantic assumption rather than an automatic endpoint.

This makes Fitch a particularly strong test for 4-PEL, but only after `K`, internal negation, knowledge absence, and possibility are kept distinct.

## Verified positive comparison gate

`PEL4/KnowledgeSemantics.lean` already contains two positive conditions:

```text
standardBoxPositive
evidenceStableKnowledgePositive
```

Lean 4.31 verifies:

```text
evidenceStableKnowledgePositive(phi)
  -> standardBoxPositive(phi).
```

It also verifies a finite contrast model with accessible values

```text
T, B
```

where ordinary positive `Box` succeeds but evidence-stable positive knowledge fails. Thus universal positive support does not by itself guarantee epistemically stable knowledge.

## Full evidence-stable knowledge candidate: next build gate

The module now adds a candidate negative component:

```text
standardBoxNegative(phi)
  := some accessible world negatively supports phi

evidenceStableKnowledgeNegative(phi)
  := not FDEValueStable(phi) OR standardBoxNegative(phi).
```

The full candidate is the FDE value

```text
K*(phi) = (K+(phi), K-(phi)).
```

The instability disjunct is essential. For example, accessible values `T` and `N` contain no negative support, but they disagree about the complete information state and should therefore fail stable knowledge.

### Candidate Knowledge Stability Principle

The new build candidate predicts that homogeneous accessible information recovers its complete four-valued status:

```text
all accessible values T -> K*(phi) = T
all accessible values F -> K*(phi) = F
all accessible values B -> K*(phi) = B
all accessible values N -> K*(phi) = N.
```

A parameterized Lean theorem attempts to prove all four cases at once.

### Candidate instability theorem

The second key target is:

```text
FDE-value instability -> K*(phi) = F.
```

Thus heterogeneity does not merely remove positive knowledge. It supplies negative epistemic support against the claim that the proposition is stably known.

If this gate builds, the resulting finite semantics has a particularly simple form:

```text
homogeneous accessible status -> recover that FDE value
heterogeneous accessible status -> F.
```

This is the working **Knowledge Stability Principle**.

## Knowledge absence must remain separate

Even if `K*` survives the semantic gates, the project will continue to distinguish:

```text
internal not K(phi)
lacksPositiveKnowledge(phi)
negative knowledge-support for phi
ignorance / not knowing whether phi.
```

The Belnap-Dunn literature explicitly treats knowledge, unknown truth, knowing whether, and factive ignorance as distinct modal notions.

## Modal possibility / knowability

Fitch also requires a possibility operator. The project should not define knowability simply as internal duality

```text
Diamond phi := not K(not phi)
```

until the semantics of internal negation around `K` is understood. In paraconsistent settings, the classical inference from necessary falsity to impossibility can fail, which is directly relevant to paraconsistent responses to Fitch.

Preferred implementation sequence:

1. define a raw accessibility-based possibility operator independently;
2. compare it formally with the De-Morgan-style dual of `K`;
3. prove equivalence only under explicit conditions, if equivalence actually holds;
4. define knowability using the intended possibility notion rather than notation-first duality.

## Tests required before Fitch

After the full knowledge-value gate, the next tests are:

```text
Factivity on reflexive frames:
  positive K(phi) -> positive phi at the actual world

Conjunction elimination:
  positive K(phi and psi) -> positive K(phi)
  positive K(phi and psi) -> positive K(psi)

Conjunction introduction / distribution:
  determine whether K(phi) and K(psi) imply K(phi and psi)

Classical recovery:
  on fully classical models, compare K with ordinary S5-style knowledge

Glut behavior:
  verify that K(phi) can be B

Gap behavior:
  verify that K(phi) can be N

Negation separation:
  compare internal not K(phi) with lacksPositiveKnowledge(phi)

Possibility duality:
  compare raw Diamond with not K(not phi).
```

Only after these tests should the actual Fitch derivation be encoded.

## Expected Fitch research question

The point is not merely to ask whether Fitch's derivation still goes through. The sharper structural-transport question is:

```text
Which preservation principle fails, or which additional impossibility assumption is required,
when knowability is transported through conjunction, knowledge, negation, and modal possibility?
```

In particular, 4-PEL should isolate whether

```text
K(p) and not K(p) => impossible
```

is a theorem of the chosen knowledge semantics or an additional classicality condition.

## Literature anchors

- Daniil Kozhemiachenko and Liubov Vashentseva, *Knowledge and ignorance in Belnap--Dunn logic*, Journal of Logic and Computation / arXiv:2309.01449.
- Yuri David Santos, *A Four-Valued Dynamic Epistemic Logic*, Journal of Logic, Language and Information 29 (2020), 451--489.
- Stanford Encyclopedia of Philosophy, *Fitch's Paradox of Knowability*, especially the sections on the standard derivation and paraconsistent revision.
- Jc Beall, work on paraconsistent responses to the knowability paradox and epistemic contradictions.

The methodological rule remains unchanged: theorem, model, interpretation, and philosophical identification must remain distinct layers.
