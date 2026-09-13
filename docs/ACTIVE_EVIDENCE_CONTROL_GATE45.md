# Gate 45 — Active Evidence Control

## Research question

Can the Gate-44 Markov bridge be extended from passively receiving a realized evidence formula to an agent that actively chooses what to investigate, while still distinguishing the chosen information-seeking action from the evidence outcome it produces?

## Main distinction

Gate 45 separates:

1. **Acquisition plan** — the agent chooses an epistemic action such as observing a target formula, querying a source, testing a claim, or running an experimental procedure.
2. **Realized evidence** — executing that plan may produce one or more 4PEL formulas that are then passed to the verified Conditionalization dynamics.

This prevents a conceptual mistake: choosing an experiment is not the same as choosing its result.

## Formal objects

`EpistemicAcquisitionPlan Source Procedure Atom Ag` has four constructors:

- `observe φ`
- `querySource source φ`
- `test φ`
- `experiment procedure φ`

`ActiveEvidenceSemantics Plan Atom Ag` supplies a relation

```text
Produces : Plan → Formula Atom Ag → Prop
```

so a fixed plan may have one or several possible realized evidence formulas.

`ActiveEvidencePlanStep sem m plan out` holds when the plan can produce some evidence `E` and Gate 44 verifies the realized transition

```text
m --E--> out.
```

## Verified results

### Availability implies a successor

If at least one possible outcome of a chosen plan is Conditionalization-admissible in the current model, then the plan has at least one realized successor.

### Functional acquisition recovers determinism

If the acquisition semantics is `OutcomeFunctional`, then one plan cannot produce two distinct evidence formulas. In that case:

```text
same complete present state + same acquisition plan
    → same next complete state.
```

This lifts the Gate-44 deterministic Markov bridge from realized evidence actions to agent-selected acquisition plans.

A pure state-feedback policy

```text
Model W Ag Atom → Plan
```

therefore also induces a deterministic transition rule under outcome-functional acquisition semantics.

### Outcome uncertainty is represented explicitly

`polarAcquisitionSemantics` allows a plan aimed at `φ` to produce either `φ` or `¬φ`. Lean proves that this semantics is not outcome-functional already for an atomic target. Thus Gate 45 formally distinguishes control over **what is investigated** from control over **what is discovered**.

## Concrete active-choice witness

Gate 45 reuses the concrete DynamicInstability model from the Recovery research program.

Two plans are available at exactly the same recovered initial state:

```text
safe plan       = observe p
disruptive plan = observe e
```

Under direct-realization semantics:

- the safe plan reaches `Gate29RecoveryPreservingUpdated`, which satisfies Compositional Recovery for `B p`;
- the disruptive plan reaches `DynamicInstabilityUpdated`, which does not satisfy Compositional Recovery for `B p`.

Hence the selected information-acquisition plan can alter the Recovery trajectory from the same starting epistemic state.

This is the first verified point in the project where the question is no longer only

> What happens when evidence arrives?

but also

> Which evidence does the agent choose to seek?

## Boundary and no-overclaim

Gate 45 is **not** yet an MDP or POMDP.

It does not provide:

- probabilities over possible evidence outcomes;
- rewards or utilities;
- information-acquisition costs;
- source reliability;
- experimental noise models;
- policy optimality;
- a stochastic kernel.

`querySource`, `test`, and `experiment` are typed acquisition plans, not yet calibrated scientific instruments.

Product Update remains separate because it changes the world type from `W` to `W × Act`; the Gate-44/45 fixed-state Markov bridge uses `Model W Ag Atom` as a stable state type.

## Next research direction

Gate 46 should add an explicit epistemic objective or reward layer and test whether a policy rewarded only for Recovery can rationally select information that protects Recovery while avoiding disruptive but informative evidence. That would create a formally testable bridge to confirmation bias, reward misspecification, and active information avoidance.
