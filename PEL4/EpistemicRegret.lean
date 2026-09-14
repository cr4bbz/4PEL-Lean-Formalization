import PEL4.ValueOfInformation

namespace PEL4

/-!
# Gate 52: epistemic regret

Gate 49 gave a Bellman-optimal finite-horizon value. Gate 52 uses that optimum
as a benchmark and measures how much value an explicit epistemic control
schedule leaves on the table.

The central witness is timing-sensitive: immediate exploration reaches the
Bellman optimum with zero regret, while delaying the same exploratory move by
one decision misses the robustness deadline and incurs strictly positive regret.
-/

/-- Accumulated reward of an explicit deterministic action schedule. -/
def finiteScheduleReturn
    {State Action : Type}
    (process : FiniteEpistemicDecisionProcess State Action) :
    State -> List Action -> Nat
  | _, [] => 0
  | s, a :: rest =>
      process.reward s a +
        finiteScheduleReturn process (process.transition s a) rest

/-- Regret of an explicit schedule relative to the Bellman optimum for the same
finite horizon. -/
def finiteScheduleRegret
    {State Action : Type}
    (process : FiniteEpistemicDecisionProcess State Action)
    (s : State) (schedule : List Action) : Nat :=
  finiteBellmanValue process schedule.length s -
    finiteScheduleReturn process s schedule

/-- Immediate exploration followed by exploitation attains the Gate-49
three-step optimum. -/
def gate52ImmediateExploreSchedule : List Gate48Action :=
  [.explore, .exploit, .exploit]

/-- The same exploratory action delayed by one decision. -/
def gate52DelayedExploreSchedule : List Gate48Action :=
  [.exploit, .explore, .exploit]

/-- Pure exploitation over the same horizon. -/
def gate52AlwaysExploitSchedule : List Gate48Action :=
  [.exploit, .exploit, .exploit]

theorem gate52_immediate_explore_return :
    finiteScheduleReturn gate49Process .start gate52ImmediateExploreSchedule = 4 := by
  native_decide

theorem gate52_delayed_explore_return :
    finiteScheduleReturn gate49Process .start gate52DelayedExploreSchedule = 1 := by
  native_decide

theorem gate52_always_exploit_return :
    finiteScheduleReturn gate49Process .start gate52AlwaysExploitSchedule = 3 := by
  native_decide

/-- Immediate exploration has zero regret at the three-step horizon. -/
theorem gate52_immediate_exploration_zero_regret :
    finiteScheduleRegret gate49Process .start gate52ImmediateExploreSchedule = 0 := by
  native_decide

/-- Delaying exploration by one decision incurs regret three. -/
theorem gate52_delayed_exploration_regret_eq_three :
    finiteScheduleRegret gate49Process .start gate52DelayedExploreSchedule = 3 := by
  native_decide

/-- Pure exploitation is suboptimal too, but in this witness it loses less
three-step reward than destabilizing only after the robustness deadline is
already unreachable. -/
theorem gate52_always_exploit_regret_eq_one :
    finiteScheduleRegret gate49Process .start gate52AlwaysExploitSchedule = 1 := by
  native_decide

/-- The timing result: moving the exploratory action one step later changes
regret from zero to a strictly positive amount. -/
theorem gate52_delaying_exploration_strictly_increases_regret :
    finiteScheduleRegret gate49Process .start gate52DelayedExploreSchedule >
      finiteScheduleRegret gate49Process .start gate52ImmediateExploreSchedule := by
  native_decide

/-- The delayed schedule also reproduces Gate 48's missed robustness deadline. -/
theorem gate52_delayed_schedule_misses_robust_endpoint :
    gate48Run .start gate52DelayedExploreSchedule = .integrating := by
  rfl

/-- Main Gate-52 theorem: epistemic regret is deadline-sensitive. The same
exploratory move can be optimal when taken immediately and costly when postponed. -/
theorem gate52_deadline_sensitive_epistemic_regret :
    finiteScheduleRegret gate49Process .start gate52ImmediateExploreSchedule = 0 ∧
    finiteScheduleRegret gate49Process .start gate52DelayedExploreSchedule = 3 ∧
    gate48Run .start gate52DelayedExploreSchedule = .integrating := by
  exact ⟨gate52_immediate_exploration_zero_regret,
    gate52_delayed_exploration_regret_eq_three,
    gate52_delayed_schedule_misses_robust_endpoint⟩

/-!
## Gate-52 boundary

Regret is relative to the explicit Gate-49 reward and horizon. It is not a
universal measure of irrationality, truth loss, or moral blame. The verified
claim is structural: once a finite epistemic objective has a Bellman optimum,
delaying information acquisition can have a precisely measurable opportunity
cost, and that cost can arise solely from missing a robustness deadline.
-/

end PEL4
