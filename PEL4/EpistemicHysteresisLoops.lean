import PEL4.StrongHysteresisBoundary

namespace PEL4

/-!
# Gate 42: Epistemic hysteresis loops

Gate 33 established endogenous-evidence hysteresis: reversing two evidence
updates can change Recovery because an earlier update changes the positive
extension of later belief-dependent evidence. Gate 39 then showed that this
history sensitivity requires no hidden memory register: the current full model
is sufficient for every future Conditionalization schedule.

Gate 42 asks a different question. Can an evidence controller leave an anchor
formula `P`, visit another evidence formula `Q`, and return to the same anchor
label `P`, while the full epistemic model fails to return to the state it had at
the first visit to `P`?

We call this a **control-loop displacement**. The terminology is deliberately
weaker than genuine differential-geometric holonomy. The verified object is a
finite Conditionalization loop in evidence-control space together with a
nonzero displacement in epistemic model space.
-/

/-- A two-leg control loop is entered at an anchor evidence formula `P`, then
visits `Q`, and finally returns to the same syntactic anchor `P`.

`atAnchor` is the epistemic state after the first visit to `P`; `endpoint` is
the state after the round trip `Q ; P`. -/
structure EvidenceControlLoop
    {W Ag Atom : Type} [DecidableEq W]
    (start : Model W Ag Atom)
    (P Q : Formula Atom Ag) where
  atAnchor : Model W Ag Atom
  endpoint : Model W Ag Atom
  enterAnchor : ConditionalizationScheduleRun start [P] atAnchor
  roundTrip : ConditionalizationScheduleRun atAnchor [Q, P] endpoint

/-- A control loop is epistemically nontrivial when returning to the same
syntactic anchor does not return the full epistemic model to its anchor state. -/
def EvidenceControlLoop.Nontrivial
    {W Ag Atom : Type} [DecidableEq W]
    {start : Model W Ag Atom}
    {P Q : Formula Atom Ag}
    (loop : EvidenceControlLoop start P Q) : Prop :=
  loop.atAnchor ≠ loop.endpoint

/-- Gate 39 supplies the exact no-hidden-memory boundary for loop phenomena.
If a control loop really closes in full model space, then any common future
Conditionalization schedule has exactly the same endpoint on both sides. -/
theorem evidenceControlLoop_exactClosure_erases_history
    {W Ag Atom : Type} [DecidableEq W]
    {start : Model W Ag Atom}
    {P Q : Formula Atom Ag}
    (loop : EvidenceControlLoop start P Q)
    (hCloses : loop.atAnchor = loop.endpoint)
    {future : List (Formula Atom Ag)}
    {outAnchor outEndpoint : Model W Ag Atom}
    (runAnchor : ConditionalizationScheduleRun
      loop.atAnchor future outAnchor)
    (runEndpoint : ConditionalizationScheduleRun
      loop.endpoint future outEndpoint) :
    outAnchor = outEndpoint := by
  exact same_present_same_future hCloses runAnchor runEndpoint

/-! ## Gate-33 model reused as a sharp loop witness -/

/-- Returning to belief evidence `B p` after the fractured state `B p ; e` is
admissible. At that point the positive extension of `B p` has already shrunk. -/
theorem gate42_belP_after_bel_then_e_admissible :
    ConditionalizationAdmissible Gate33BelThenE gate33BelPEvidence := by
  constructor
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel
  · intro ag w
    cases ag
    cases w <;> decide +kernel

/-- Endpoint of the closed evidence-control schedule `B p ; e ; B p`. -/
def Gate42BelEThenBel :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate33BelThenE gate33BelPEvidence
    gate42_belP_after_bel_then_e_admissible

/-- The first visit to anchor `B p` has homogeneous belief profile `T/T/T`. -/
theorem gate42_anchor_belP_profile :
    evalModal Gate33BelFirst DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate33BelFirst DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate33BelFirst DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- After the round trip `e ; B p`, the same anchor formula again has a
homogeneous `T/T/T` profile. -/
theorem gate42_endpoint_belP_profile :
    evalModal Gate42BelEThenBel DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate42BelEThenBel DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate42BelEThenBel DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- The anchor state is in compositional Recovery. -/
theorem gate42_anchor_recovered :
    ModalFormula.CompositionalRecovery
      Gate33BelFirst dynamicInstabilityBelP := by
  intro w
  constructor
  · intro u _
    cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rcases gate42_anchor_belP_profile with ⟨ha, hb, hc⟩
    cases w
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate33BelFirst DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityP ha
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate33BelFirst DynamicInstabilityAgent.i
        DynamicInstabilityWorld.b dynamicInstabilityP hb
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate33BelFirst DynamicInstabilityAgent.i
        DynamicInstabilityWorld.c dynamicInstabilityP hc

/-- The endpoint after returning to the same anchor label is again in Recovery. -/
theorem gate42_endpoint_recovered :
    ModalFormula.CompositionalRecovery
      Gate42BelEThenBel dynamicInstabilityBelP := by
  intro w
  constructor
  · intro u _
    cases u
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rcases gate42_endpoint_belP_profile with ⟨ha, hb, hc⟩
    cases w
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate42BelEThenBel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.a dynamicInstabilityP ha
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate42BelEThenBel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.b dynamicInstabilityP hb
    · exact beliefThresholdComplete_of_evalModal_bel_eq_T
        Gate42BelEThenBel DynamicInstabilityAgent.i
        DynamicInstabilityWorld.c dynamicInstabilityP hc

/-- The semantic content of the returning anchor has changed. Initially `B p`
has the full extension `{a,b,c}`; immediately before the return visit it has
shrunk to `{a,c}`. -/
theorem gate42_return_anchor_extension_shrinks :
    conditionalizationEvidenceEvent Gate33BelThenE
      DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence =
      [DynamicInstabilityWorld.a, DynamicInstabilityWorld.c] := by
  decide +kernel

/-- Same syntactic anchor, different extensional meaning on return. -/
theorem gate42_anchor_semantics_changed_on_return :
    conditionalizationEvidenceEvent DynamicInstabilityModel
        DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence ≠
      conditionalizationEvidenceEvent Gate33BelThenE
        DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate33BelPEvidence := by
  rw [gate33_belP_event_initial_full, gate42_return_anchor_extension_shrinks]
  decide

/-- The atomic evidence event `{a,b}` is a convenient probability probe. -/
def gate42AtomicEvidenceEvent : FiniteSet DynamicInstabilityWorld :=
  [DynamicInstabilityWorld.a, DynamicInstabilityWorld.b]

/-- At the first visit to `B p`, the probability of atomic evidence `e` at
source world `a` is still the prior value `4/5`. -/
theorem gate42_anchor_atomicEvidence_mass :
    Gate33BelFirst.mu DynamicInstabilityAgent.i DynamicInstabilityWorld.a
      gate42AtomicEvidenceEvent = (4 : Rat) / 5 := by
  decide +kernel

/-- After the closed control loop `B p ; e ; B p`, atomic evidence `e` has
probability one at source world `a`. -/
theorem gate42_endpoint_atomicEvidence_mass :
    Gate42BelEThenBel.mu DynamicInstabilityAgent.i DynamicInstabilityWorld.a
      gate42AtomicEvidenceEvent = 1 := by
  decide +kernel

/-- The loop therefore does not close in full epistemic state space, even
though it returns to the same evidence-control label and recovers the same
Recovery status. -/
theorem gate42_loop_has_nontrivial_epistemic_displacement :
    Gate33BelFirst ≠ Gate42BelEThenBel := by
  intro hEq
  have hMass := congrArg
    (fun model :
      Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom =>
        model.mu DynamicInstabilityAgent.i DynamicInstabilityWorld.a
          gate42AtomicEvidenceEvent) hEq
  rw [gate42_anchor_atomicEvidence_mass,
      gate42_endpoint_atomicEvidence_mass] at hMass
  have hNe : (4 : Rat) / 5 ≠ 1 := by decide
  exact hNe hMass

/-- Concrete schedule run entering the anchor `B p`. -/
def gate42_enter_anchor_run :
    ConditionalizationScheduleRun DynamicInstabilityModel
      [gate33BelPEvidence] Gate33BelFirst := by
  exact ConditionalizationScheduleRun.cons gate33_belP_initial_admissible
    (ConditionalizationScheduleRun.nil Gate33BelFirst)

/-- Concrete round trip from anchor `B p` through `e` and back to `B p`. -/
def gate42_roundTrip_run :
    ConditionalizationScheduleRun Gate33BelFirst
      [dynamicInstabilityEvidence, gate33BelPEvidence] Gate42BelEThenBel := by
  exact ConditionalizationScheduleRun.cons gate33_e_after_belP_admissible
    (ConditionalizationScheduleRun.cons
      gate42_belP_after_bel_then_e_admissible
      (ConditionalizationScheduleRun.nil Gate42BelEThenBel))

/-- Gate-42 control-loop object. -/
def gate42ControlLoop :
    EvidenceControlLoop DynamicInstabilityModel
      gate33BelPEvidence dynamicInstabilityEvidence :=
  { atAnchor := Gate33BelFirst
  , endpoint := Gate42BelEThenBel
  , enterAnchor := gate42_enter_anchor_run
  , roundTrip := gate42_roundTrip_run
  }

/-- The Gate-42 loop is nontrivial in full epistemic model space. -/
theorem gate42_controlLoop_nontrivial :
    gate42ControlLoop.Nontrivial := by
  exact gate42_loop_has_nontrivial_epistemic_displacement

/-- The sharp phenomenon: Recovery itself traces a closed excursion
`Recovery -> non-Recovery -> Recovery`, while the full epistemic state fails to
return to its anchor. -/
theorem gate42_recovery_loop_closes_but_model_does_not :
    ModalFormula.CompositionalRecovery
        Gate33BelFirst dynamicInstabilityBelP ∧
    ¬ ModalFormula.CompositionalRecovery
        Gate33BelThenE dynamicInstabilityBelP ∧
    ModalFormula.CompositionalRecovery
        Gate42BelEThenBel dynamicInstabilityBelP ∧
    Gate33BelFirst ≠ Gate42BelEThenBel := by
  exact ⟨gate42_anchor_recovered,
    gate33_bel_then_e_not_recovered,
    gate42_endpoint_recovered,
    gate42_loop_has_nontrivial_epistemic_displacement⟩

/-!
## Gate-42 conclusion

The verified loop has three levels:

```text
control:   Bp ------ e ------ Bp       (same syntactic anchor)
Recovery:  true --- false --- true     (status loop closes)
model:     M_P -------------- M'_P     (full state does not close)
```

The displacement is observable in the local probability measure: the event
`{a,b}` has mass `4/5` at the first anchor visit and mass `1` after the round
trip. At the same time the returning `B p` anchor has changed its positive
extension from `{a,b,c}` to `{a,c}`.

This is **holonomy-like** only in the controlled sense of path-dependent
transport around a closed evidence-control loop. No manifold, connection,
curvature tensor, or geometric holonomy theorem is claimed.

Gate 39 supplies the complementary boundary: if the full model itself closes,
then every identical future schedule coalesces exactly. Hence there is no hidden
history beyond the endpoint model. The loop memory is stored in the displaced
current epistemic state itself.
-/

end PEL4