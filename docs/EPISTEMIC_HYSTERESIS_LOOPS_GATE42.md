# Gate 42 — Epistemic Hysteresis Loops

## Research question

Can an evidence controller leave an anchor formula `P`, visit another evidence formula `Q`, and return to the same syntactic anchor `P` while the full epistemic model fails to return to the state it had at the first anchor visit?

Gate 42 answers **yes** for the existing Gate-33 conditionalization witness.

The result is intentionally described as **holonomy-like**, not as geometric holonomy. The formal object is a finite evidence-control loop with path-dependent displacement in epistemic model space. No manifold, connection, curvature tensor, or differential-geometric theorem is assumed.

## Formal object

`EvidenceControlLoop start P Q` stores:

- an anchor state `atAnchor` reached by the schedule `[P]`,
- an endpoint reached from that anchor by `[Q, P]`,
- the corresponding `ConditionalizationScheduleRun` proofs.

The loop is `Nontrivial` when

```text
atAnchor ≠ endpoint.
```

Thus the control label returns to `P`, while the internal epistemic state need not.

## No-hidden-memory boundary

Gate 39 is reused directly:

```lean
evidenceControlLoop_exactClosure_erases_history
```

If the full model does return exactly to its anchor state, then every common future Conditionalization schedule has exactly the same endpoint from both states.

Therefore any persistent loop effect must be encoded in the displaced current model itself. There is no additional hidden history register.

## Concrete Gate-33 loop

Use:

```text
P = B p
Q = e
```

The closed control schedule is

```text
B p ; e ; B p.
```

At the first `B p` anchor visit, the belief profile is

```text
T / T / T
```

and compositional Recovery holds.

After `e`, the profile becomes

```text
T / N / T
```

and Recovery fails.

After returning to `B p`, the profile becomes

```text
T / T / T
```

and Recovery holds again.

Hence Recovery traces the closed excursion

```text
true -> false -> true.
```

## Nontrivial epistemic displacement

Despite Recovery returning to its original Boolean status, the full epistemic model does not return.

Use the atomic evidence event

```text
{a,b}.
```

At source world `a`:

```text
first Bp anchor:  mu({a,b}) = 4/5
loop endpoint:    mu({a,b}) = 1
```

Therefore

```text
Gate33BelFirst ≠ Gate42BelEThenBel.
```

The endpoint has retained path-dependent information in its probability measure.

## Semantic feedback on the returning anchor

The same syntactic formula `B p` also has different positive extensions at the two anchor visits:

```text
initial Bp extension:   {a,b,c}
return Bp extension:    {a,c}
```

So the controller returns to the same formula label, but not to the same extensional evidence event.

This connects Gate 42 directly to Gate 40: semantic extension feedback is the mechanism that makes the loop nontrivial.

## Main theorem

```lean
gate42_recovery_loop_closes_but_model_does_not
```

verifies simultaneously:

1. Recovery at the first anchor,
2. non-Recovery after the excursion through `e`,
3. Recovery after returning to `B p`,
4. inequality of the first-anchor and endpoint models.

Schematic form:

```text
control:   Bp ------ e ------ Bp
Recovery:  true --- false --- true
model:     M_P -------------- M'_P
                           with M_P ≠ M'_P
```

## Interpretation

Gate 42 separates three notions that would otherwise be easy to conflate:

- returning to the same **control label**,
- returning to the same **Recovery status**,
- returning to the same **full epistemic state**.

The first two can close while the third remains open.

This is the precise 4PEL sense in which a closed evidence-control path can carry a nonzero epistemic displacement.

## No-overclaim boundary

Gate 42 does **not** establish:

- differential-geometric holonomy,
- a manifold structure on epistemic models,
- a connection or curvature tensor,
- that every semantic-feedback loop is nontrivial,
- that Recovery closure implies semantic closure.

It establishes one finite, formally verified path-dependent loop witness plus an exact-closure theorem inherited from state sufficiency.
