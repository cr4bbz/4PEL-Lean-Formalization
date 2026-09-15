import PEL4.RationalUnresolvedness

namespace PEL4

/-!
# Gate 114: general identifiability criterion

Gates 110 and 111 gave opposite finite witnesses. Gate 110 showed that a decoder
cannot be uniformly correct when two target-different worlds share one
observation; Gate 111 restored correctness by refining the observation channel.
Gate 114 isolates the general structure behind both results.

A truth-guaranteeing decoder exists exactly when the target is constant on every
fiber of the observation map. Thus full hidden-world identification is stronger
than necessary: worlds may remain observationally aliased whenever they require
the same target verdict.
-/

/-- A decoder is truth-guaranteeing when it reconstructs the target value at every
hidden world from observation alone. -/
def Gate114TruthGuaranteeing
    {World Observation Verdict : Type}
    (observe : World → Observation)
    (target : World → Verdict)
    (decode : Observation → Verdict) : Prop :=
  ∀ world : World, decode (observe world) = target world

/-- Target-aware identifiability: any two worlds in the same observation fiber
must require the same target verdict. -/
def Gate114FiberConsistent
    {World Observation Verdict : Type}
    (observe : World → Observation)
    (target : World → Verdict) : Prop :=
  ∀ left right : World,
    observe left = observe right → target left = target right

/-- Any uniformly correct decoder forces target constancy on observation fibers. -/
theorem gate114_decoder_implies_fiber_consistent
    {World Observation Verdict : Type}
    (observe : World → Observation)
    (target : World → Verdict)
    (decode : Observation → Verdict)
    (hDecode : Gate114TruthGuaranteeing observe target decode) :
    Gate114FiberConsistent observe target := by
  intro left right hObservation
  calc
    target left = decode (observe left) := (hDecode left).symm
    _ = decode (observe right) := congrArg decode hObservation
    _ = target right := hDecode right

/-- Construct a decoder from a fiber-consistency proof. Values outside the image
of `observe` are irrelevant to correctness and receive the default verdict. -/
noncomputable def gate114Decoder
    {World Observation Verdict : Type}
    [Inhabited Verdict]
    (observe : World → Observation)
    (target : World → Verdict)
    (_hFiber : Gate114FiberConsistent observe target) : Observation → Verdict :=
  fun observation =>
    if hExists : ∃ world : World, observe world = observation then
      target (Classical.choose hExists)
    else
      default

/-- The decoder constructed from a fiber-consistency proof is uniformly correct. -/
theorem gate114_constructed_decoder_truth_guaranteeing
    {World Observation Verdict : Type}
    [Inhabited Verdict]
    (observe : World → Observation)
    (target : World → Verdict)
    (hFiber : Gate114FiberConsistent observe target) :
    Gate114TruthGuaranteeing observe target
      (gate114Decoder observe target hFiber) := by
  intro world
  unfold gate114Decoder
  have hExists : ∃ candidate : World, observe candidate = observe world :=
    ⟨world, rfl⟩
  rw [dif_pos hExists]
  exact hFiber (Classical.choose hExists) world (Classical.choose_spec hExists)

/-- Main Gate-114 theorem: target-aware fiber consistency is necessary and
sufficient for existence of a truth-guaranteeing observation decoder. -/
theorem gate114_truth_guaranteeing_decoder_iff_fiber_consistent
    {World Observation Verdict : Type}
    [Inhabited Verdict]
    (observe : World → Observation)
    (target : World → Verdict) :
    (∃ decode : Observation → Verdict,
      Gate114TruthGuaranteeing observe target decode) ↔
      Gate114FiberConsistent observe target := by
  constructor
  · rintro ⟨decode, hDecode⟩
    exact gate114_decoder_implies_fiber_consistent observe target decode hDecode
  · intro hFiber
    exact ⟨gate114Decoder observe target hFiber,
      gate114_constructed_decoder_truth_guaranteeing observe target hFiber⟩

/-- Gate 110 is exactly a violation of the general fiber criterion. -/
theorem gate114_gate110_fails_fiber_consistency :
    ¬ Gate114FiberConsistent gate110Observe gate110Target := by
  intro hFiber
  have hTargets := hFiber Gate110HiddenWorld.positive Gate110HiddenWorld.negative
    gate110_worlds_are_observationally_aliased
  exact gate110_aliased_worlds_require_different_targets hTargets

/-- Gate 111's active diagnostic satisfies the general criterion because its
existing decoder is truth-guaranteeing. -/
theorem gate114_gate111_diagnostic_is_fiber_consistent :
    Gate114FiberConsistent
      (gate111Observe Gate111Experiment.disambiguate) gate110Target := by
  exact gate114_decoder_implies_fiber_consistent
    (gate111Observe Gate111Experiment.disambiguate)
    gate110Target gate111Decode gate111_diagnostic_truth_guaranteeing

/-- The old impossibility and the active recovery are therefore two instances of
one abstract criterion rather than unrelated finite examples. -/
theorem gate114_gates110_111_are_instances :
    (¬ Gate114FiberConsistent gate110Observe gate110Target) ∧
    Gate114FiberConsistent
      (gate111Observe Gate111Experiment.disambiguate) gate110Target := by
  exact ⟨gate114_gate110_fails_fiber_consistency,
    gate114_gate111_diagnostic_is_fiber_consistent⟩

/-!
## Gate-114 interpretation boundary

The reverse direction constructs a decoder using classical choice and a default
value for observations outside the image of the observation map. This is an
existence theorem, not an efficient decoder-synthesis algorithm.

The criterion is target-aware. It does not require the observation map to identify
hidden worlds themselves. Aliased worlds are harmless whenever the requested
4PEL target is identical across the entire fiber. Gate 115 uses this distinction
to study minimal experiment families for target identification rather than full
state reconstruction.
-/

end PEL4
