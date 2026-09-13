import PEL4.EpistemicHysteresisLoops

namespace PEL4

/-!
# Gate 43: Discrete epistemic curvature by loop composition

Gate 42 verified a single closed evidence-control loop whose control label and
Recovery status return while the full epistemic model does not. Gate 43 asks a
strictly stronger question: can two such control excursions fail to commute?

The finite analogue studied here is deliberately weaker than differential-
geometric curvature. We compare two schedules that start at one epistemic
state, perform the same two excursions `P` and `Q`, return to the same syntactic
anchor `A` after each excursion, but compose the two loops in opposite orders:

    A -> P -> A -> Q -> A
    A -> Q -> A -> P -> A

A difference between the two endpoint models is called a discrete epistemic
curvature witness. No manifold, connection, tangent bundle, or curvature tensor
is claimed.
-/

/-- Two opposite compositions of the same pair of anchored evidence loops. -/
structure EpistemicLoopCommutator
    {W Ag Atom : Type} [DecidableEq W]
    (start : Model W Ag Atom)
    (A P Q : Formula Atom Ag) where
  outPQ : Model W Ag Atom
  outQP : Model W Ag Atom
  runPQ : ConditionalizationScheduleRun start [P, A, Q, A] outPQ
  runQP : ConditionalizationScheduleRun start [Q, A, P, A] outQP

/-- The loop commutator is nontrivial when reversing loop order changes the
full epistemic endpoint. -/
def EpistemicLoopCommutator.Noncommuting
    {W Ag Atom : Type} [DecidableEq W]
    {start : Model W Ag Atom}
    {A P Q : Formula Atom Ag}
    (comm : EpistemicLoopCommutator start A P Q) : Prop :=
  comm.outPQ ≠ comm.outQP

/-- Gate-43 finite curvature predicate: there exists an admissible pair of
anchored loop compositions with different full epistemic endpoints. -/
def DiscreteEpistemicCurvatureAt
    {W Ag Atom : Type} [DecidableEq W]
    (start : Model W Ag Atom)
    (A P Q : Formula Atom Ag) : Prop :=
  ∃ comm : EpistemicLoopCommutator start A P Q, comm.Noncommuting

/-- Gate 39 rules out nondeterministic artifacts. For a fixed loop order, every
admissible execution has exactly the endpoint stored by the commutator. -/
theorem EpistemicLoopCommutator.pq_endpoint_unique
    {W Ag Atom : Type} [DecidableEq W]
    {start : Model W Ag Atom}
    {A P Q : Formula Atom Ag}
    (comm : EpistemicLoopCommutator start A P Q)
    {out : Model W Ag Atom}
    (run : ConditionalizationScheduleRun start [P, A, Q, A] out) :
    out = comm.outPQ := by
  exact conditionalizationScheduleRun_deterministic run comm.runPQ

/-- The opposite fixed order is deterministic for the same reason. -/
theorem EpistemicLoopCommutator.qp_endpoint_unique
    {W Ag Atom : Type} [DecidableEq W]
    {start : Model W Ag Atom}
    {A P Q : Formula Atom Ag}
    (comm : EpistemicLoopCommutator start A P Q)
    {out : Model W Ag Atom}
    (run : ConditionalizationScheduleRun start [Q, A, P, A] out) :
    out = comm.outQP := by
  exact conditionalizationScheduleRun_deterministic run comm.runQP

/-! ## Concrete Gate-43 witness -/

/-- A syntactic anchor that is classically true at every world of the concrete
instability model. Since conditionalization changes only probabilities, its
truth profile remains fixed throughout the witness. -/
def gate43NeutralAnchor :
    Formula DynamicInstabilityAtom DynamicInstabilityAgent :=
  Formula.or
    (Formula.prop DynamicInstabilityAtom.p)
    (Formula.not (Formula.prop DynamicInstabilityAtom.p))

/-- The neutral anchor has the full positive extension initially. -/
theorem gate43_neutral_anchor_initial_full :
    conditionalizationEvidenceEvent DynamicInstabilityModel
      DynamicInstabilityAgent.i DynamicInstabilityWorld.a gate43NeutralAnchor =
      [DynamicInstabilityWorld.a,
       DynamicInstabilityWorld.b,
       DynamicInstabilityWorld.c] := by
  decide +kernel

/-- Return to the neutral anchor after the first `B p` excursion. -/
theorem gate43_anchor_after_bel_admissible :
    ConditionalizationAdmissible Gate33BelFirst gate43NeutralAnchor := by
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

def Gate43BelAnchor :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate33BelFirst gate43NeutralAnchor
    gate43_anchor_after_bel_admissible

/-- The atomic excursion remains admissible after returning to the anchor. -/
theorem gate43_e_after_bel_anchor_admissible :
    ConditionalizationAdmissible Gate43BelAnchor dynamicInstabilityEvidence := by
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

def Gate43BelAnchorE :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate43BelAnchor dynamicInstabilityEvidence
    gate43_e_after_bel_anchor_admissible

/-- Final return to the neutral anchor for the order `B p ; A ; e ; A`. -/
theorem gate43_anchor_after_bel_e_admissible :
    ConditionalizationAdmissible Gate43BelAnchorE gate43NeutralAnchor := by
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

def Gate43BelThenEEndpoint :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate43BelAnchorE gate43NeutralAnchor
    gate43_anchor_after_bel_e_admissible

/-- Return to the neutral anchor after the first atomic `e` excursion. -/
theorem gate43_anchor_after_e_admissible :
    ConditionalizationAdmissible Gate33EFirst gate43NeutralAnchor := by
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

def Gate43EAnchor :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate33EFirst gate43NeutralAnchor
    gate43_anchor_after_e_admissible

/-- Belief-dependent evidence remains admissible after `e` and the neutral
anchor return. -/
theorem gate43_bel_after_e_anchor_admissible :
    ConditionalizationAdmissible Gate43EAnchor gate33BelPEvidence := by
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

def Gate43EAnchorBel :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate43EAnchor gate33BelPEvidence
    gate43_bel_after_e_anchor_admissible

/-- Final return to the neutral anchor for the order `e ; A ; B p ; A`. -/
theorem gate43_anchor_after_e_bel_admissible :
    ConditionalizationAdmissible Gate43EAnchorBel gate43NeutralAnchor := by
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

def Gate43EThenBelEndpoint :
    Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom :=
  conditionalize Gate43EAnchorBel gate43NeutralAnchor
    gate43_anchor_after_e_bel_admissible

/-- The `B p`-first loop composition ends with the familiar fractured profile. -/
theorem gate43_bel_then_e_endpoint_profile :
    evalModal Gate43BelThenEEndpoint DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate43BelThenEEndpoint DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.N ∧
    evalModal Gate43BelThenEEndpoint DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- Reversing the two anchored loops restores the homogeneous profile. -/
theorem gate43_e_then_bel_endpoint_profile :
    evalModal Gate43EThenBelEndpoint DynamicInstabilityWorld.a
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate43EThenBelEndpoint DynamicInstabilityWorld.b
        dynamicInstabilityBelP = FDEValue.T ∧
    evalModal Gate43EThenBelEndpoint DynamicInstabilityWorld.c
        dynamicInstabilityBelP = FDEValue.T := by
  decide +kernel

/-- The opposite loop compositions are observably different at world `b`. -/
theorem gate43_loop_orders_modally_diverge :
    evalModal Gate43BelThenEEndpoint DynamicInstabilityWorld.b
        dynamicInstabilityBelP ≠
      evalModal Gate43EThenBelEndpoint DynamicInstabilityWorld.b
        dynamicInstabilityBelP := by
  rw [gate43_bel_then_e_endpoint_profile.2.1,
      gate43_e_then_bel_endpoint_profile.2.1]
  decide

/-- Hence the full endpoint models of the two closed control paths differ. -/
theorem gate43_loop_order_endpoints_differ :
    Gate43BelThenEEndpoint ≠ Gate43EThenBelEndpoint := by
  intro hEq
  have hEval := congrArg
    (fun model :
      Model DynamicInstabilityWorld DynamicInstabilityAgent DynamicInstabilityAtom =>
        evalModal model DynamicInstabilityWorld.b dynamicInstabilityBelP) hEq
  exact gate43_loop_orders_modally_diverge hEval

/-- Concrete schedule for the loop order `B p` then `e`. -/
def gate43_run_bel_then_e :
    ConditionalizationScheduleRun DynamicInstabilityModel
      [gate33BelPEvidence, gate43NeutralAnchor,
       dynamicInstabilityEvidence, gate43NeutralAnchor]
      Gate43BelThenEEndpoint := by
  exact ConditionalizationScheduleRun.cons gate33_belP_initial_admissible
    (ConditionalizationScheduleRun.cons gate43_anchor_after_bel_admissible
      (ConditionalizationScheduleRun.cons gate43_e_after_bel_anchor_admissible
        (ConditionalizationScheduleRun.cons gate43_anchor_after_bel_e_admissible
          (ConditionalizationScheduleRun.nil Gate43BelThenEEndpoint))))

/-- Concrete schedule for the reversed loop order `e` then `B p`. -/
def gate43_run_e_then_bel :
    ConditionalizationScheduleRun DynamicInstabilityModel
      [dynamicInstabilityEvidence, gate43NeutralAnchor,
       gate33BelPEvidence, gate43NeutralAnchor]
      Gate43EThenBelEndpoint := by
  exact ConditionalizationScheduleRun.cons dynamic_instability_evidence_admissible
    (ConditionalizationScheduleRun.cons gate43_anchor_after_e_admissible
      (ConditionalizationScheduleRun.cons gate43_bel_after_e_anchor_admissible
        (ConditionalizationScheduleRun.cons gate43_anchor_after_e_bel_admissible
          (ConditionalizationScheduleRun.nil Gate43EThenBelEndpoint))))

/-- Gate-43 loop-commutator object. -/
def gate43LoopCommutator :
    EpistemicLoopCommutator DynamicInstabilityModel
      gate43NeutralAnchor gate33BelPEvidence dynamicInstabilityEvidence :=
  { outPQ := Gate43BelThenEEndpoint
  , outQP := Gate43EThenBelEndpoint
  , runPQ := gate43_run_bel_then_e
  , runQP := gate43_run_e_then_bel
  }

/-- The loop commutator is nonzero in full epistemic model space. -/
theorem gate43_loop_commutator_noncommuting :
    gate43LoopCommutator.Noncommuting := by
  exact gate43_loop_order_endpoints_differ

/-- Main Gate-43 theorem: the DynamicInstability model carries a concrete
finite discrete epistemic-curvature witness. -/
theorem gate43_discrete_epistemic_curvature :
    DiscreteEpistemicCurvatureAt DynamicInstabilityModel
      gate43NeutralAnchor gate33BelPEvidence dynamicInstabilityEvidence := by
  exact ⟨gate43LoopCommutator, gate43_loop_commutator_noncommuting⟩

/-!
## Gate-43 conclusion

The two control paths

    A -> Bp -> A -> e  -> A
    A -> e  -> A -> Bp -> A

use exactly the same loop ingredients and return to the same syntactic neutral
anchor `A`. Nevertheless their endpoint models disagree, already on the modal
observation `B p` at world `b` (`N` versus `T`). Gate 39 additionally proves
that each fixed schedule has a unique endpoint, so this is order-sensitive
transport rather than nondeterminism.

The safe geometric language is therefore **discrete epistemic curvature
witness** or **nonzero epistemic loop commutator**. This formalization does not
establish differential-geometric curvature.
-/

end PEL4
