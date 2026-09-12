# Gate 40 — Strong Hysteresis Boundary

## Research question

Gate 33 established a genuine Recovery hysteresis witness: the same syntactic evidence ingredients `{e, B p}` can yield different Recovery outcomes when their order is reversed. Gate 36 then showed that belief-free evidence is extension-stable, while Gate 38 proved confluence on that static fragment.

Gate 40 asks for the exact semantic boundary. Is the presence of a belief operator itself enough to explain hysteresis, or is the real mechanism the change of an evidence formula's extension under an earlier update?

## Result

The boundary is semantic rather than syntactic.

For arbitrary evidence formulas `P` and `Q`, possibly containing belief operators, assume probability integrity, mutual sequential admissibility, and mutual evidence-extension stability:

- the extension of `P` is unchanged after updating by `Q`;
- the extension of `Q` is unchanged after updating by `P`.

Then the two update orders are modally observationally equivalent:

```text
P ; Q  ~obs  Q ; P
```

Consequently every current modal formula has the same compositional Recovery status in both endpoints.

Formally, Gate 40 proves:

- `conditionalize_two_extensionStable_measure_eq_on_event`
- `conditionalize_two_extensionStable_observationEquivalent`
- `conditionalize_two_extensionStable_recovery_confluent`
- `recovery_hysteresis_implies_extension_feedback`
- `gate40_gate33_violates_mutual_extension_stability`

## Necessary condition for Recovery hysteresis

The central contrapositive is:

```text
Recovery hysteresis
  => not (P stable after Q and Q stable after P)
```

So a concrete Recovery-hysteresis witness must contain semantic feedback in at least one direction: one update must change what the other evidence formula positively denotes.

This does **not** mean every belief-containing formula is order-sensitive. A belief formula that happens to keep the same extension remains on the confluent side of the boundary.

## Relation to Gate 33

Gate 33 realizes exactly the required failure. Initially `B p` has the full positive extension in the dynamic-instability model. After conditioning on `e`, its positive extension shrinks. Thus `B p` is not extension-stable under the `e` update.

The mechanism is therefore not mysterious noncommutativity of Bayesian division. It is endogenous evidence semantics:

```text
current model
  -> evaluates future evidence content
  -> update changes current model
  -> same syntactic evidence can denote a different event
```

## Research interpretation

Gate 40 separates two notions that should not be conflated:

1. **belief-dependent syntax**: a formula contains `B`;
2. **semantic feedback**: an earlier update changes the positive extension of later evidence.

Only the second is necessary for the verified Recovery hysteresis phenomenon.

This gives the research program a cleaner phase boundary:

```text
extension-stable evidence
  -> confluence island

extension-sensitive evidence
  -> hysteresis becomes possible
```

The word "possible" matters. Extension feedback is necessary for the Gate-40 notion of two-step Recovery hysteresis, not sufficient by itself.

## No-overclaim boundary

Gate 40 does not prove that every extension-sensitive pair produces hysteresis, nor does it prove global nonconfluence for arbitrary schedules. It proves a semantic no-go theorem: if both evidence extensions remain fixed under the opposite update, Recovery hysteresis cannot occur.
