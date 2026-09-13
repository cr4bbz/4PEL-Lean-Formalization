import PEL4.MarkovBridge
import PEL4.EpistemicPathDependence

namespace PEL4

/-!
# Gate 45: active evidence control

Gate 44 treated a realized evidence formula as the control input of a
deterministic transition system. Gate 45 separates two notions that should not
be conflated:

* the epistemic acquisition plan selected by an agent, and
* the evidence formula actually produced by executing that plan.

An observation can be modeled as outcome-functional, while a query, test, or
experiment may admit several possible evidence outcomes. Once a realized
formula is fixed, Gate 44 supplies the deterministic 4PEL update.
-/

/-- Agent-selectable ways of seeking information. `Source` labels queried
sources; `Procedure` labels experiments or measurement procedures. Each plan
also carries the proposition it is aimed at investigating. -/
inductive EpistemicAcquisitionPlan
    (Source Procedure Atom Ag : Type) where
  | observe (target : Formula Atom Ag)
  | querySource (source : Source) (target : Formula Atom Ag)
  | test (target : Formula Atom Ag)
  | experiment (procedure : Procedure) (target : Formula Atom Ag)

namespace EpistemicAcquisitionPlan

/-- The formula an acquisition plan is directed at investigating. -/
def target
    {Source Procedure Atom Ag : Type} :
    EpistemicAcquisitionPlan Source Procedure Atom Ag -> Formula Atom Ag
  | .observe φ => φ
  | .querySource _ φ => φ
  | .test φ => φ
  | .experiment _ φ => φ

end EpistemicAcquisitionPlan

/-- Semantics for an information-acquisition interface. `Produces plan E`
means that executing `plan` may realize evidence formula `E`. This relation is
allowed to be nondeterministic. -/
structure ActiveEvidenceSemantics (Plan Atom Ag : Type) where
  Produces : Plan -> Formula Atom Ag -> Prop

namespace ActiveEvidenceSemantics

/-- An acquisition semantics is outcome-functional when a fixed chosen plan can
produce at most one realized evidence formula. -/
def OutcomeFunctional
    {Plan Atom Ag : Type}
    (sem : ActiveEvidenceSemantics Plan Atom Ag) : Prop :=
  ∀ {plan : Plan} {E₁ E₂ : Formula Atom Ag},
    sem.Produces plan E₁ -> sem.Produces plan E₂ -> E₁ = E₂

end ActiveEvidenceSemantics

/-- A chosen acquisition plan can move the current 4PEL state to `out` when it
may produce some evidence formula whose realized Conditionalization step reaches
`out`. -/
def ActiveEvidencePlanStep
    {W Plan Ag Atom : Type} [DecidableEq W]
    (sem : ActiveEvidenceSemantics Plan Atom Ag)
    (m : Model W Ag Atom) (plan : Plan) (out : Model W Ag Atom) : Prop :=
  ∃ E : Formula Atom Ag,
    sem.Produces plan E ∧ ControlledEpistemicStep m E out

/-- State-dependent executability: at least one possible evidence outcome of the
chosen plan is admissible for Conditionalization in the current model. -/
def ActiveEvidencePlanAvailableAt
    {W Plan Ag Atom : Type} [DecidableEq W]
    (sem : ActiveEvidenceSemantics Plan Atom Ag)
    (m : Model W Ag Atom) (plan : Plan) : Prop :=
  ∃ E : Formula Atom Ag,
    sem.Produces plan E ∧ ConditionalizationAdmissible m E

/-- Every available acquisition plan has at least one realized successor. -/
theorem activeEvidencePlanStep_exists_of_available
    {W Plan Ag Atom : Type} [DecidableEq W]
    (sem : ActiveEvidenceSemantics Plan Atom Ag)
    (m : Model W Ag Atom) (plan : Plan)
    (hAvailable : ActiveEvidencePlanAvailableAt sem m plan) :
    ∃ out : Model W Ag Atom, ActiveEvidencePlanStep sem m plan out := by
  rcases hAvailable with ⟨E, hProduces, hAdm⟩
  refine ⟨conditionalize m E hAdm, E, hProduces, ?_⟩
  exact controlledEpistemicStep_of_admissible m E hAdm

/-- Gate-44 determinism survives at the plan level whenever the acquisition
semantics itself has a unique realized evidence outcome. -/
theorem activeEvidencePlanStep_deterministic_of_functional
    {W Plan Ag Atom : Type} [DecidableEq W]
    {sem : ActiveEvidenceSemantics Plan Atom Ag}
    (hFunctional : sem.OutcomeFunctional)
    {m : Model W Ag Atom} {plan : Plan}
    {out₁ out₂ : Model W Ag Atom}
    (step₁ : ActiveEvidencePlanStep sem m plan out₁)
    (step₂ : ActiveEvidencePlanStep sem m plan out₂) :
    out₁ = out₂ := by
  rcases step₁ with ⟨E₁, hProduces₁, hStep₁⟩
  rcases step₂ with ⟨E₂, hProduces₂, hStep₂⟩
  have hEvidence : E₁ = E₂ := hFunctional hProduces₁ hProduces₂
  subst E₂
  exact controlledEpistemicStep_deterministic hStep₁ hStep₂

/-- Markov bridge for active acquisition: under outcome-functional acquisition,
two identical complete present models plus the same selected plan have the same
next full model. -/
theorem activeEvidencePlanStep_same_present_of_functional
    {W Plan Ag Atom : Type} [DecidableEq W]
    {sem : ActiveEvidenceSemantics Plan Atom Ag}
    (hFunctional : sem.OutcomeFunctional)
    {m n : Model W Ag Atom} {plan : Plan}
    {outM outN : Model W Ag Atom}
    (hPresent : m = n)
    (stepM : ActiveEvidencePlanStep sem m plan outM)
    (stepN : ActiveEvidencePlanStep sem n plan outN) :
    outM = outN := by
  subst n
  exact activeEvidencePlanStep_deterministic_of_functional
    hFunctional stepM stepN

/-- A policy chooses one acquisition plan as a function of the current complete
4PEL model. -/
abbrev ActiveEvidencePolicy
    (W Plan Ag Atom : Type) [DecidableEq W] :=
  Model W Ag Atom -> Plan

/-- One transition under a state-feedback acquisition policy. -/
def ActiveEvidencePolicyStep
    {W Plan Ag Atom : Type} [DecidableEq W]
    (sem : ActiveEvidenceSemantics Plan Atom Ag)
    (policy : ActiveEvidencePolicy W Plan Ag Atom)
    (m out : Model W Ag Atom) : Prop :=
  ActiveEvidencePlanStep sem m (policy m) out

/-- Outcome-functional acquisition turns every pure state-feedback policy into
a deterministic epistemic transition rule. -/
theorem activeEvidencePolicyStep_deterministic_of_functional
    {W Plan Ag Atom : Type} [DecidableEq W]
    {sem : ActiveEvidenceSemantics Plan Atom Ag}
    (hFunctional : sem.OutcomeFunctional)
    (policy : ActiveEvidencePolicy W Plan Ag Atom)
    {m out₁ out₂ : Model W Ag Atom}
    (step₁ : ActiveEvidencePolicyStep sem policy m out₁)
    (step₂ : ActiveEvidencePolicyStep sem policy m out₂) :
    out₁ = out₂ := by
  exact activeEvidencePlanStep_deterministic_of_functional
    hFunctional step₁ step₂

/-! ## Two acquisition semantics -/

/-- Direct-realization semantics: the selected plan itself determines the
realized evidence formula, namely its target. This is suitable for actions such
as deliberately inspecting a known record or selecting which already-available
piece of evidence to condition on. -/
def directAcquisitionSemantics
    {Source Procedure Atom Ag : Type} :
    ActiveEvidenceSemantics
      (EpistemicAcquisitionPlan Source Procedure Atom Ag) Atom Ag where
  Produces := fun plan E => E = plan.target

/-- Direct-realization semantics is outcome-functional. -/
theorem directAcquisitionSemantics_functional
    {Source Procedure Atom Ag : Type} :
    (directAcquisitionSemantics
      (Source := Source) (Procedure := Procedure)
      (Atom := Atom) (Ag := Ag)).OutcomeFunctional := by
  intro plan E₁ E₂ h₁ h₂
  exact h₁.trans h₂.symm

/-- Polar semantics: an information-seeking plan aimed at `φ` may return either
`φ` or `¬φ` as its realized evidence. This deliberately models uncertainty of
outcome separately from the agent's choice of what to investigate. -/
def polarAcquisitionSemantics
    {Source Procedure Atom Ag : Type} :
    ActiveEvidenceSemantics
      (EpistemicAcquisitionPlan Source Procedure Atom Ag) Atom Ag where
  Produces := fun plan E =>
    E = plan.target ∨ E = Formula.not plan.target

/-- Polar acquisition is genuinely non-functional already for an atomic target:
the same observation plan admits syntactically distinct positive and negative
realizations. -/
theorem polarAcquisitionSemantics_not_functional
    {Source Procedure Atom Ag : Type} (p : Atom) :
    ¬ (polarAcquisitionSemantics
      (Source := Source) (Procedure := Procedure)
      (Atom := Atom) (Ag := Ag)).OutcomeFunctional := by
  intro hFunctional
  let plan : EpistemicAcquisitionPlan Source Procedure Atom Ag :=
    .observe (Formula.prop p)
  have hPos :
      (polarAcquisitionSemantics
        (Source := Source) (Procedure := Procedure)
        (Atom := Atom) (Ag := Ag)).Produces plan (Formula.prop p) := by
    exact Or.inl rfl
  have hNeg :
      (polarAcquisitionSemantics
        (Source := Source) (Procedure := Procedure)
        (Atom := Atom) (Ag := Ag)).Produces plan
          (Formula.not (Formula.prop p)) := by
    exact Or.inr rfl
  have hEq : Formula.prop p = Formula.not (Formula.prop p) :=
    hFunctional hPos hNeg
  cases hEq

/-! ## Concrete Gate-45 witness: active choice changes Recovery -/

abbrev Gate45Plan :=
  EpistemicAcquisitionPlan Unit Unit
    DynamicInstabilityAtom DynamicInstabilityAgent

/-- Active choice of the Gate-29 Recovery-preserving observation. -/
def gate45SafePlan : Gate45Plan :=
  .observe gate29RecoveryPreservingEvidence

/-- Active choice of the Gate-11 destabilizing evidence observation. -/
def gate45DisruptivePlan : Gate45Plan :=
  .observe dynamicInstabilityEvidence

/-- Direct realization semantics specialized to the concrete Gate-45 plans. -/
def gate45DirectSemantics :
    ActiveEvidenceSemantics Gate45Plan
      DynamicInstabilityAtom DynamicInstabilityAgent :=
  directAcquisitionSemantics

/-- The safe plan is executable at the common initial model. -/
theorem gate45_safePlan_available :
    ActiveEvidencePlanAvailableAt gate45DirectSemantics
      DynamicInstabilityModel gate45SafePlan := by
  exact ⟨gate29RecoveryPreservingEvidence, rfl,
    gate29_recoveryPreservingEvidence_admissible⟩

/-- The disruptive plan is also executable at exactly the same initial model. -/
theorem gate45_disruptivePlan_available :
    ActiveEvidencePlanAvailableAt gate45DirectSemantics
      DynamicInstabilityModel gate45DisruptivePlan := by
  exact ⟨dynamicInstabilityEvidence, rfl,
    dynamic_instability_evidence_admissible⟩

/-- Executing the safe plan reaches the known Recovery-preserving successor. -/
theorem gate45_safePlan_step :
    ActiveEvidencePlanStep gate45DirectSemantics
      DynamicInstabilityModel gate45SafePlan
      Gate29RecoveryPreservingUpdated := by
  exact ⟨gate29RecoveryPreservingEvidence, rfl,
    controlledEpistemicStep_of_admissible
      DynamicInstabilityModel gate29RecoveryPreservingEvidence
      gate29_recoveryPreservingEvidence_admissible⟩

/-- Executing the disruptive plan reaches the known Recovery-destroying
successor. -/
theorem gate45_disruptivePlan_step :
    ActiveEvidencePlanStep gate45DirectSemantics
      DynamicInstabilityModel gate45DisruptivePlan
      DynamicInstabilityUpdated := by
  exact ⟨dynamicInstabilityEvidence, rfl,
    controlledEpistemicStep_of_admissible
      DynamicInstabilityModel dynamicInstabilityEvidence
      dynamic_instability_evidence_admissible⟩

/-- Main concrete active-control witness: from one and the same recovered 4PEL
state, two available agent-selected observation plans lead respectively to a
Recovered and a Non-Recovered successor. -/
theorem gate45_active_choice_splits_recovery :
    ActiveEvidencePlanAvailableAt gate45DirectSemantics
        DynamicInstabilityModel gate45SafePlan ∧
    ActiveEvidencePlanAvailableAt gate45DirectSemantics
        DynamicInstabilityModel gate45DisruptivePlan ∧
    ActiveEvidencePlanStep gate45DirectSemantics
        DynamicInstabilityModel gate45SafePlan
        Gate29RecoveryPreservingUpdated ∧
    ActiveEvidencePlanStep gate45DirectSemantics
        DynamicInstabilityModel gate45DisruptivePlan
        DynamicInstabilityUpdated ∧
    ModalFormula.CompositionalRecovery
        Gate29RecoveryPreservingUpdated dynamicInstabilityBelP ∧
    ¬ ModalFormula.CompositionalRecovery
        DynamicInstabilityUpdated dynamicInstabilityBelP := by
  exact ⟨gate45_safePlan_available,
    gate45_disruptivePlan_available,
    gate45_safePlan_step,
    gate45_disruptivePlan_step,
    gate29_recoveryPreserving_update_recovered,
    dynamic_instability_belP_not_recovered_after⟩

/-!
## Gate-45 boundary

Gate 45 verifies active information acquisition as a control layer over 4PEL.
The agent may choose *what to investigate*, and an acquisition semantics says
which evidence formulas may be realized. Once evidence is realized,
Conditionalization remains deterministic as in Gate 44.

This is still not an MDP or POMDP. There are no outcome probabilities, rewards,
costs, utilities, or optimality criteria. `querySource`, `test`, and `experiment`
are typed acquisition plans only; source reliability and experimental noise are
not yet modeled. Product Update also remains separate because it changes the
world type from `W` to `W × Act` rather than staying inside the fixed-state type
used by the Gate-44 Markov bridge.
-/

end PEL4
