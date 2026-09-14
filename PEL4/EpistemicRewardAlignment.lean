import PEL4.EpistemicRegret

namespace PEL4

/-!
# Gate 53: epistemic reward alignment

Gate 46 exhibited reward misspecification; Gates 47–52 showed why robust
Recovery and timely exploration can matter over a longer horizon. Gate 53 asks
for a simple sufficient condition on the reward itself under which the
three-step controller prefers the robustness-producing exploratory schedule.

The reward family has two parameters:

* `recoveryWeight`: reward for ending a step in ordinary Recovery;
* `robustBonus`: additional reward for ending a step in the verified robust
  Recovery state.

For the Gate-48 three-step witness, immediate exploration receives
`recoveryWeight + robustBonus`, whereas pure exploitation receives three copies
of `recoveryWeight`. Hence a robust bonus larger than two ordinary Recovery
rewards is sufficient to reverse the misspecified preference.
-/

/-- Parameterized state reward separating ordinary Recovery from robust
Recovery. -/
def gate53StateReward (recoveryWeight robustBonus : Nat) : Gate47State -> Nat
  | .fragile => recoveryWeight
  | .robust => recoveryWeight + robustBonus
  | _ => 0

/-- Parameterized deterministic decision process on the existing Gate-48
transition system. -/
def gate53Process (recoveryWeight robustBonus : Nat) :
    FiniteEpistemicDecisionProcess Gate47State Gate48Action where
  actions := [.exploit, .explore]
  transition := gate48Transition
  reward := fun s a =>
    gate53StateReward recoveryWeight robustBonus (gate48Transition s a)

/-- Reward-alignment condition for this finite witness. -/
def Gate53RobustnessAligned (recoveryWeight robustBonus : Nat) : Prop :=
  recoveryWeight + recoveryWeight < robustBonus

/-- Exact return of immediate exploration under the parameterized reward. -/
theorem gate53_immediate_explore_return_formula
    (recoveryWeight robustBonus : Nat) :
    finiteScheduleReturn (gate53Process recoveryWeight robustBonus) .start
      gate52ImmediateExploreSchedule = recoveryWeight + robustBonus := by
  simp [finiteScheduleReturn, gate53Process, gate53StateReward,
    gate48Transition, gate52ImmediateExploreSchedule]

/-- Exact return of pure exploitation under the same reward. -/
theorem gate53_always_exploit_return_formula
    (recoveryWeight robustBonus : Nat) :
    finiteScheduleReturn (gate53Process recoveryWeight robustBonus) .start
      gate52AlwaysExploitSchedule =
        recoveryWeight + (recoveryWeight + recoveryWeight) := by
  simp [finiteScheduleReturn, gate53Process, gate53StateReward,
    gate48Transition, gate52AlwaysExploitSchedule]

/-- Sufficient reward-alignment theorem: if the robust bonus exceeds two
ordinary Recovery rewards, immediate exploration strictly dominates pure
exploitation over the three-step horizon. -/
theorem gate53_alignment_threshold_selects_exploration
    (recoveryWeight robustBonus : Nat)
    (hAligned : Gate53RobustnessAligned recoveryWeight robustBonus) :
    finiteScheduleReturn (gate53Process recoveryWeight robustBonus) .start
        gate52ImmediateExploreSchedule >
      finiteScheduleReturn (gate53Process recoveryWeight robustBonus) .start
        gate52AlwaysExploitSchedule := by
  rw [gate53_immediate_explore_return_formula,
    gate53_always_exploit_return_formula]
  unfold Gate53RobustnessAligned at hAligned
  omega

/-- Complementary boundary: if the robust bonus is at most two ordinary
Recovery rewards, pure exploitation is at least as good as immediate
exploration in this witness. -/
theorem gate53_below_threshold_exploitation_not_worse
    (recoveryWeight robustBonus : Nat)
    (hBelow : robustBonus ≤ recoveryWeight + recoveryWeight) :
    finiteScheduleReturn (gate53Process recoveryWeight robustBonus) .start
        gate52AlwaysExploitSchedule ≥
      finiteScheduleReturn (gate53Process recoveryWeight robustBonus) .start
        gate52ImmediateExploreSchedule := by
  rw [gate53_immediate_explore_return_formula,
    gate53_always_exploit_return_formula]
  omega

/-- A pure immediate-Recovery proxy (`robustBonus = 0`) reproduces the
exploitative preference. -/
theorem gate53_naive_recovery_reward_prefers_exploitation :
    finiteScheduleReturn (gate53Process 1 0) .start gate52AlwaysExploitSchedule >
      finiteScheduleReturn (gate53Process 1 0) .start
        gate52ImmediateExploreSchedule := by
  native_decide

/-- A concrete aligned reward (`recoveryWeight = 1`, `robustBonus = 3`) selects
immediate exploration. -/
theorem gate53_aligned_reward_prefers_exploration :
    finiteScheduleReturn (gate53Process 1 3) .start gate52ImmediateExploreSchedule >
      finiteScheduleReturn (gate53Process 1 3) .start gate52AlwaysExploitSchedule := by
  native_decide

/-- Main Gate-53 result: the same transition system exhibits opposite optimal
preferences under a misspecified Recovery-only reward and under a reward that
sufficiently values robust Recovery. -/
theorem gate53_reward_design_controls_epistemic_policy :
    finiteScheduleReturn (gate53Process 1 0) .start gate52AlwaysExploitSchedule >
        finiteScheduleReturn (gate53Process 1 0) .start
          gate52ImmediateExploreSchedule ∧
    finiteScheduleReturn (gate53Process 1 3) .start gate52ImmediateExploreSchedule >
        finiteScheduleReturn (gate53Process 1 3) .start
          gate52AlwaysExploitSchedule := by
  exact ⟨gate53_naive_recovery_reward_prefers_exploitation,
    gate53_aligned_reward_prefers_exploration⟩

/-!
## Gate-53 boundary

This is a reward-alignment theorem relative to the verified finite robustness
objective. It does not prove alignment with correspondence truth, human values,
or every epistemically desirable property. The threshold is specific to this
three-step witness and reward family. What is established is the structural
point: reward design alone can switch the optimal epistemic policy from
information avoidance to timely exploration, and a sufficient threshold can be
proved rather than guessed.
-/

end PEL4
