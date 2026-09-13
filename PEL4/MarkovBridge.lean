import PEL4.DiscreteEpistemicCurvature
import PEL4.ConditionalizationAtomicIdempotence

namespace PEL4

/-!
# Gate 44: Markov bridge

Gate 39 proved state sufficiency for arbitrary finite Conditionalization
schedules: once the current full `Model` is fixed, a common admissible future
schedule has a unique endpoint. Gate 44 repackages the one-step fragment of
that result as a controlled transition system.

This is deliberately not yet an MDP. There is no reward function and no
stochastic transition kernel. The verified bridge is the deterministic control
skeleton on which later decision-theoretic structure may be added.
-/

/-- An epistemic control action is an evidence formula selected for the next
Conditionalization step. -/
abbrev EpistemicControlAction (Atom Ag : Type) := Formula Atom Ag

/-- The controlled state is the complete current 4PEL model. -/
abbrev EpistemicControlState (W Ag Atom : Type) := Model W Ag Atom

/-- One controlled epistemic step is exactly a singleton Conditionalization
schedule. Admissibility is therefore carried by the schedule-run witness. -/
def ControlledEpistemicStep
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (action : Formula Atom Ag)
    (out : Model W Ag Atom) : Prop :=
  ConditionalizationScheduleRun m [action] out

/-- Every admissible evidence formula induces a controlled step. -/
theorem controlledEpistemicStep_of_admissible
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (action : Formula Atom Ag)
    (hAdm : ConditionalizationAdmissible m action) :
    ControlledEpistemicStep m action (conditionalize m action hAdm) := by
  exact ConditionalizationScheduleRun.cons hAdm
    (ConditionalizationScheduleRun.nil (conditionalize m action hAdm))

/-- Fixed full state plus fixed action has a unique next full state. -/
theorem controlledEpistemicStep_deterministic
    {W Ag Atom : Type} [DecidableEq W]
    {m out₁ out₂ : Model W Ag Atom}
    {action : Formula Atom Ag}
    (step₁ : ControlledEpistemicStep m action out₁)
    (step₂ : ControlledEpistemicStep m action out₂) :
    out₁ = out₂ := by
  exact conditionalizationScheduleRun_deterministic step₁ step₂

/-- A minimal deterministic controlled transition system. This is the formal
bridge target for Gate 44, intentionally weaker than an MDP. -/
structure DeterministicControlledTransitionSystem (State Action : Type) where
  Step : State → Action → State → Prop
  deterministic : ∀ {s : State} {a : Action} {t₁ t₂ : State},
    Step s a t₁ → Step s a t₂ → t₁ = t₂

/-- Conditionalization equips full 4PEL models with a deterministic controlled
transition-system structure. -/
def fourPELConditionalizationControlSystem
    {W Ag Atom : Type} [DecidableEq W] :
    DeterministicControlledTransitionSystem
      (Model W Ag Atom) (Formula Atom Ag) :=
  { Step := ControlledEpistemicStep
  , deterministic := by
      intro s a t₁ t₂ h₁ h₂
      exact controlledEpistemicStep_deterministic h₁ h₂
  }

/-- Full-state Markov sufficiency for one controlled step. Two histories that
have reached the same complete present model cannot be distinguished by the
same next epistemic action. -/
theorem controlledEpistemicStep_same_present_same_action
    {W Ag Atom : Type} [DecidableEq W]
    {m n outM outN : Model W Ag Atom}
    {action : Formula Atom Ag}
    (hPresent : m = n)
    (stepM : ControlledEpistemicStep m action outM)
    (stepN : ControlledEpistemicStep n action outN) :
    outM = outN := by
  exact same_present_same_future hPresent stepM stepN

/-- Explicit history-erasure form of the Markov bridge. The past schedules may
be entirely different. Once their endpoints coincide, a common next action has
one common next state. -/
theorem controlledEpistemicStep_history_irrelevant_after_merge
    {W Ag Atom : Type} [DecidableEq W]
    {start₁ start₂ current₁ current₂ out₁ out₂ : Model W Ag Atom}
    {past₁ past₂ : List (Formula Atom Ag)}
    {action : Formula Atom Ag}
    (history₁ : ConditionalizationScheduleRun start₁ past₁ current₁)
    (history₂ : ConditionalizationScheduleRun start₂ past₂ current₂)
    (hMerge : EpistemicHistoriesMergeAt history₁ history₂)
    (step₁ : ControlledEpistemicStep current₁ action out₁)
    (step₂ : ControlledEpistemicStep current₂ action out₂) :
    out₁ = out₂ := by
  exact controlledEpistemicStep_same_present_same_action hMerge step₁ step₂

/-- The one-step theorem extends immediately to every common finite action
sequence because actions are represented by evidence schedules. -/
theorem controlledEpistemicFuture_same_present_same_actions
    {W Ag Atom : Type} [DecidableEq W]
    {m n outM outN : Model W Ag Atom}
    {actions : List (Formula Atom Ag)}
    (hPresent : m = n)
    (runM : ConditionalizationScheduleRun m actions outM)
    (runN : ConditionalizationScheduleRun n actions outN) :
    outM = outN := by
  exact same_present_same_future hPresent runM runN

/-! ## Concrete compression witness: one atomic observation versus two -/

/-- A one-update atomic history. -/
def gate44_atomic_history_once
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p)) :
    ConditionalizationScheduleRun m [Formula.prop p]
      (conditionalize m (Formula.prop p) hAdm) := by
  exact controlledEpistemicStep_of_admissible m (Formula.prop p) hAdm

/-- A two-update history repeating the same atomic observation. -/
def gate44_atomic_history_twice
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (hRepeat := conditionalize_prop_repeat_admissible m p hAdm) :
    ConditionalizationScheduleRun m [Formula.prop p, Formula.prop p]
      (conditionalize (conditionalize m (Formula.prop p) hAdm)
        (Formula.prop p) hRepeat) := by
  exact ConditionalizationScheduleRun.cons hAdm
    (ConditionalizationScheduleRun.cons hRepeat
      (ConditionalizationScheduleRun.nil
        (conditionalize (conditionalize m (Formula.prop p) hAdm)
          (Formula.prop p) hRepeat)))

/-- The distinct one-step and two-step histories merge into exactly the same
full epistemic model by atomic idempotence. -/
theorem gate44_atomic_histories_merge
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (hRepeat := conditionalize_prop_repeat_admissible m p hAdm) :
    conditionalize m (Formula.prop p) hAdm =
      conditionalize (conditionalize m (Formula.prop p) hAdm)
        (Formula.prop p) hRepeat := by
  symm
  exact conditionalize_repeat_prop_eq m p hAdm hRepeat

/-- Sharp Markov-compression witness: after one versus two repetitions of the
same atomic observation have merged, every common admissible next action has
exactly the same endpoint. The earlier difference in history length is erased
by the current full model. -/
theorem gate44_atomic_stutter_history_erased
    {W Ag Atom : Type} [DecidableEq W]
    (m : Model W Ag Atom) (p : Atom)
    (hAdm : ConditionalizationAdmissible m (Formula.prop p))
    (hRepeat := conditionalize_prop_repeat_admissible m p hAdm)
    {action : Formula Atom Ag}
    {outOnce outTwice : Model W Ag Atom}
    (stepOnce : ControlledEpistemicStep
      (conditionalize m (Formula.prop p) hAdm) action outOnce)
    (stepTwice : ControlledEpistemicStep
      (conditionalize (conditionalize m (Formula.prop p) hAdm)
        (Formula.prop p) hRepeat) action outTwice) :
    outOnce = outTwice := by
  exact controlledEpistemicStep_same_present_same_action
    (gate44_atomic_histories_merge m p hAdm hRepeat) stepOnce stepTwice

/-!
## Gate-44 boundary

The verified object is a deterministic controlled transition system:

```text
current full model M + selected evidence action a -> unique next model M'
```

and the full-model state is Markov-sufficient in the exact history-erasure
sense above. Gate 44 does **not** yet provide an MDP: there is no reward,
policy, discount factor, or stochastic transition kernel. It also does not
claim that a coarse observable such as the Recovery Boolean is itself a
sufficient Markov state.
-/

end PEL4
