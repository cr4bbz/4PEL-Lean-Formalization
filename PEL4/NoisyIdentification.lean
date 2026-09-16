import PEL4.MinimalTargetExperimentFamily

namespace PEL4

/-!
# Gate 116: noisy identification

Gate 115 studied deterministic experiment families: once the selected observations
separated target-different worlds, a truth-guaranteeing decoder could exist. Gate
116 removes that idealization. The same signal can now occur in either hidden
world, only with different likelihoods.

The witness uses two hidden worlds with a symmetric binary sensor. A matching
signal is produced with probability `4/5`, and the misleading signal with
probability `1/5`, under a symmetric prior. Bayesian updating therefore changes
confidence without logically eliminating the alternative world.

A strict decision threshold of `9/10` is then used as an explicit bridge from
posterior confidence to a four-valued control status. One noisy sample remains
`N`; two agreeing samples cross the threshold to `T` or `F`; conflicting samples
return to `N`. Crucially, even two agreeing samples do not make the opposite world
impossible.
-/

inductive Gate116World where
  | positive
  | negative
  deriving DecidableEq, Repr

inductive Gate116Signal where
  | positive
  | negative
  deriving DecidableEq, Repr

inductive Gate116Action where
  | commitPositive
  | commitNegative
  | measureAgain
  | remainUnresolved
  deriving DecidableEq, Repr

/-- The target verdict associated with each hidden world. -/
def gate116Target : Gate116World → FDEValue
  | .positive => FDEValue.T
  | .negative => FDEValue.F

/-- Symmetric noisy sensor: `4/5` correct, `1/5` misleading. -/
def gate116SignalLikelihood : Gate116World → Gate116Signal → Rat
  | .positive, .positive => (4 : Rat) / 5
  | .positive, .negative => (1 : Rat) / 5
  | .negative, .positive => (1 : Rat) / 5
  | .negative, .negative => (4 : Rat) / 5

/-- Symmetric prior probability of the positive world. -/
def gate116PriorPositive : Rat := (1 : Rat) / 2

/-- Likelihood of an ordered signal trace conditional on a hidden world. -/
def gate116TraceLikelihood (world : Gate116World) : List Gate116Signal → Rat
  | [] => 1
  | signal :: rest =>
      gate116SignalLikelihood world signal * gate116TraceLikelihood world rest

/-- Marginal evidence of a trace under the symmetric prior. -/
def gate116TraceEvidence (trace : List Gate116Signal) : Rat :=
  gate116PriorPositive * gate116TraceLikelihood .positive trace +
    (1 - gate116PriorPositive) * gate116TraceLikelihood .negative trace

/-- Exact Bayesian posterior probability of the positive world. -/
def gate116PosteriorPositive (trace : List Gate116Signal) : Rat :=
  (gate116PriorPositive * gate116TraceLikelihood .positive trace) /
    gate116TraceEvidence trace

/-- Explicit confidence threshold used to bridge probability into a four-valued
control status. This is a modelling threshold, not a logical truth definition. -/
def gate116CommitThreshold : Rat := (9 : Rat) / 10

/-- Posterior-to-4PEL control bridge. High positive confidence yields `T`, high
negative confidence yields `F`, and the middle region remains `N`. This witness
does not introduce contradictory evidence, so `B` is not reached here. -/
def gate116PosteriorStatus (posteriorPositive : Rat) : FDEValue :=
  if posteriorPositive ≥ gate116CommitThreshold then
    FDEValue.T
  else if posteriorPositive ≤ 1 - gate116CommitThreshold then
    FDEValue.F
  else
    FDEValue.N

/-- Four-valued control status induced by an observed trace. -/
def gate116TraceStatus (trace : List Gate116Signal) : FDEValue :=
  gate116PosteriorStatus (gate116PosteriorPositive trace)

/-- A one-signal decoder would be support-correct only if every signal that has
positive probability in a world were decoded to that world's target verdict. -/
def Gate116OneSignalSupportCorrect
    (decode : Gate116Signal → FDEValue) : Prop :=
  ∀ world signal,
    gate116SignalLikelihood world signal > 0 →
      decode signal = gate116Target world

/-- The noisy channel makes every individual signal possible in both worlds. -/
theorem gate116_each_signal_has_full_support :
    gate116SignalLikelihood .positive .positive > 0 ∧
    gate116SignalLikelihood .negative .positive > 0 ∧
    gate116SignalLikelihood .positive .negative > 0 ∧
    gate116SignalLikelihood .negative .negative > 0 := by
  native_decide

/-- Therefore no deterministic one-signal decoder can be truth-guaranteeing on
channel support. The same positive signal can arise in target-`T` and target-`F`
worlds. -/
theorem gate116_no_truth_guaranteeing_one_signal_decoder :
    ¬ ∃ decode : Gate116Signal → FDEValue,
      Gate116OneSignalSupportCorrect decode := by
  rintro ⟨decode, hDecode⟩
  have hPositive := hDecode Gate116World.positive Gate116Signal.positive (by
    native_decide)
  have hNegative := hDecode Gate116World.negative Gate116Signal.positive (by
    native_decide)
  have hDifferent :
      gate116Target Gate116World.positive ≠ gate116Target Gate116World.negative := by
    native_decide
  exact hDifferent (hPositive.symm.trans hNegative)

/-- Exact posterior after one positive signal. -/
theorem gate116_one_positive_posterior :
    gate116PosteriorPositive [.positive] = (4 : Rat) / 5 := by
  native_decide

/-- Exact posterior after one negative signal. -/
theorem gate116_one_negative_posterior :
    gate116PosteriorPositive [.negative] = (1 : Rat) / 5 := by
  native_decide

/-- One noisy observation is not decisive under the `9/10` bridge. -/
theorem gate116_one_signal_remains_unresolved :
    gate116TraceStatus [.positive] = FDEValue.N ∧
    gate116TraceStatus [.negative] = FDEValue.N := by
  native_decide

/-- Two agreeing positive signals yield posterior `16/17`. -/
theorem gate116_double_positive_posterior :
    gate116PosteriorPositive [.positive, .positive] = (16 : Rat) / 17 := by
  native_decide

/-- Two agreeing negative signals yield positive-world posterior `1/17`. -/
theorem gate116_double_negative_posterior :
    gate116PosteriorPositive [.negative, .negative] = (1 : Rat) / 17 := by
  native_decide

/-- Conflicting signals exactly cancel in the symmetric witness. -/
theorem gate116_conflicting_signals_restore_half :
    gate116PosteriorPositive [.positive, .negative] = (1 : Rat) / 2 ∧
    gate116PosteriorPositive [.negative, .positive] = (1 : Rat) / 2 := by
  native_decide

/-- The confidence bridge therefore creates an `N → T/F` transition only when
the two noisy observations agree; disagreement preserves `N`. -/
theorem gate116_two_signal_statuses :
    gate116TraceStatus [.positive, .positive] = FDEValue.T ∧
    gate116TraceStatus [.negative, .negative] = FDEValue.F ∧
    gate116TraceStatus [.positive, .negative] = FDEValue.N ∧
    gate116TraceStatus [.negative, .positive] = FDEValue.N := by
  native_decide

/-- Even after two positive observations, the negative world remains possible:
its likelihood for that trace is `1/25`, not zero. -/
theorem gate116_double_positive_does_not_logically_eliminate_negative :
    gate116TraceLikelihood .negative [.positive, .positive] = (1 : Rat) / 25 ∧
    gate116TraceLikelihood .negative [.positive, .positive] > 0 := by
  native_decide

/-- Symmetrically, two negative observations do not logically eliminate the
positive world. -/
theorem gate116_double_negative_does_not_logically_eliminate_positive :
    gate116TraceLikelihood .positive [.negative, .negative] = (1 : Rat) / 25 ∧
    gate116TraceLikelihood .positive [.negative, .negative] > 0 := by
  native_decide

/-- Sequential control after one observation: because either single sample still
maps to `N`, the agent requests another measurement rather than committing. -/
def gate116AfterOneAction (signal : Gate116Signal) : Gate116Action :=
  match gate116TraceStatus [signal] with
  | FDEValue.T => .commitPositive
  | FDEValue.F => .commitNegative
  | _ => .measureAgain

/-- After two observations the controller commits only if the posterior bridge is
strict, otherwise it preserves unresolvedness. -/
def gate116AfterTwoAction (trace : List Gate116Signal) : Gate116Action :=
  match gate116TraceStatus trace with
  | FDEValue.T => .commitPositive
  | FDEValue.F => .commitNegative
  | _ => .remainUnresolved

/-- Both possible first observations trigger another measurement. -/
theorem gate116_first_sample_requests_remeasurement :
    gate116AfterOneAction .positive = .measureAgain ∧
    gate116AfterOneAction .negative = .measureAgain := by
  native_decide

/-- Two agreeing observations trigger directional commitment, while conflicting
observations retain the epistemic gap. -/
theorem gate116_second_sample_controls_commitment :
    gate116AfterTwoAction [.positive, .positive] = .commitPositive ∧
    gate116AfterTwoAction [.negative, .negative] = .commitNegative ∧
    gate116AfterTwoAction [.positive, .negative] = .remainUnresolved ∧
    gate116AfterTwoAction [.negative, .positive] = .remainUnresolved := by
  native_decide

/-- Main Gate-116 result: noisy observations can increase confidence enough for a
threshold policy to move from `N` to `T/F`, but they do not restore the logical
truth guarantees available in deterministic Gate 114/115 identification. -/
theorem gate116_noisy_identification :
    (¬ ∃ decode : Gate116Signal → FDEValue,
      Gate116OneSignalSupportCorrect decode) ∧
    gate116PosteriorPositive [.positive] = (4 : Rat) / 5 ∧
    gate116TraceStatus [.positive] = FDEValue.N ∧
    gate116PosteriorPositive [.positive, .positive] = (16 : Rat) / 17 ∧
    gate116TraceStatus [.positive, .positive] = FDEValue.T ∧
    gate116TraceStatus [.positive, .negative] = FDEValue.N ∧
    gate116TraceLikelihood .negative [.positive, .positive] > 0 := by
  exact ⟨gate116_no_truth_guaranteeing_one_signal_decoder,
    gate116_one_positive_posterior,
    gate116_one_signal_remains_unresolved.1,
    gate116_double_positive_posterior,
    gate116_two_signal_statuses.1,
    gate116_two_signal_statuses.2.2.1,
    gate116_double_positive_does_not_logically_eliminate_negative.2⟩

/-!
## Gate-116 interpretation boundary

The `9/10` confidence threshold is an explicit control convention. Gate 116 does
not identify posterior probability with logical truth, nor does it claim that two
agreeing samples make a proposition true. In fact the opposite-world likelihood
is proved strictly positive after two agreeing observations.

Likewise, the witness assumes a known, symmetric and conditionally independent
sensor with fixed `4/5` reliability. It does not yet price repeated measurement,
learn sensor reliability, model correlated noise, or optimize stopping time.
Those are natural later gates.

The formal gain is a clean separation between two notions that deterministic
identifiability collapses: `epistemic confidence sufficient for control` and
`logical elimination of alternatives`. Under noise, the first can occur while the
second provably does not.
-/

end PEL4
