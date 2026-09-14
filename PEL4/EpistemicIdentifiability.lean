import PEL4.ActiveEpistemicSensing

namespace PEL4

/-!
# Gate 65: epistemic identifiability

Gate 64 made sensing an active choice. Gate 65 asks a prior structural question:
which hidden epistemic states can the available sensor family distinguish at all?
Identifiability is therefore always relative to the declared experiments and
observation channel.
-/

/-- Two hidden states are observationally equivalent relative to the Gate-64
sensor family when every available sensor assigns exactly the same likelihood
to every possible observation. -/
def Gate65ObservationallyEquivalent
    (left right : Gate47State) : Prop :=
  ∀ sensor observation,
    gate64SensorLikelihood sensor left observation =
      gate64SensorLikelihood sensor right observation

/-- Two hidden states are identifiable relative to the available sensor family
when some sensor/observation pair separates their likelihoods. -/
def Gate65Identifiable (left right : Gate47State) : Prop :=
  ∃ sensor observation,
    gate64SensorLikelihood sensor left observation ≠
      gate64SensorLikelihood sensor right observation

/-- Equality of the coarse Gate-55 observation implies observational equivalence
for every Gate-64 sensor, because those sensors differ only in reliability, not
in which hidden property they measure. -/
theorem gate65_same_coarse_status_implies_observational_equivalence
    {left right : Gate47State}
    (h : gate55Observe left = gate55Observe right) :
    Gate65ObservationallyEquivalent left right := by
  intro sensor observation
  cases sensor <;>
    simp [gate64SensorLikelihood, h]

/-- The fragile and robust states remain observationally aliased under the entire
Gate-64 sensor menu. More precision about the same coarse bit does not recover
the hidden robustness distinction. -/
theorem gate65_fragile_robust_observationally_equivalent :
    Gate65ObservationallyEquivalent .fragile .robust := by
  exact gate65_same_coarse_status_implies_observational_equivalence
    gate55_fragile_robust_same_observation

/-- Hence no sensor in the current family identifies fragile versus robust. -/
theorem gate65_fragile_robust_not_identifiable :
    ¬ Gate65Identifiable .fragile .robust := by
  intro hIdent
  rcases hIdent with ⟨sensor, observation, hNe⟩
  exact hNe (gate65_fragile_robust_observationally_equivalent sensor observation)

/-- The aliasing is epistemically substantive: the two indistinguishable hidden
states disagree on stress-robust Recovery. -/
theorem gate65_aliased_states_differ_in_robustness :
    ¬ Gate47RobustRecovery .fragile ∧ Gate47RobustRecovery .robust := by
  exact ⟨gate47_fragile_not_robust, gate47_robust_is_robust⟩

/-- They also disagree on the Gate-54 truth/calibration bridge. -/
theorem gate65_aliased_states_differ_in_truth_alignment :
    ¬ gate54TruthAligned .fragile ∧ gate54TruthAligned .robust := by
  exact ⟨gate54_recovery_alone_does_not_imply_truth.2,
    gate54_robust_state_truth_aligned⟩

/-- Robust and destabilized are distinguishable. The precise sensor's Recovery
likelihood is 9/10 in the robust state and 1/10 in the destabilized state. -/
theorem gate65_robust_destabilized_identifiable :
    Gate65Identifiable .robust .destabilized := by
  refine ⟨.precise, .recovery, ?_⟩
  native_decide

/-- Concrete separating likelihoods for the identifiable pair. -/
theorem gate65_robust_destabilized_likelihoods :
    gate64SensorLikelihood .precise .robust .recovery = (9 : Rat) / 10 ∧
    gate64SensorLikelihood .precise .destabilized .recovery = (1 : Rat) / 10 := by
  constructor <;> native_decide

/-- Observational equivalence and identifiability cannot both hold. -/
theorem gate65_equivalence_excludes_identifiability
    {left right : Gate47State}
    (hEq : Gate65ObservationallyEquivalent left right) :
    ¬ Gate65Identifiable left right := by
  intro hIdent
  rcases hIdent with ⟨sensor, observation, hNe⟩
  exact hNe (hEq sensor observation)

/-- Main Gate-65 boundary. The current sensor family can distinguish robust from
destabilized, but cannot distinguish fragile from robust even though those states
differ in robustness and truth alignment. Identifiability is therefore a property
of the state pair together with the available experiment class. -/
theorem gate65_epistemic_identifiability_boundary :
    Gate65ObservationallyEquivalent .fragile .robust ∧
    ¬ Gate65Identifiable .fragile .robust ∧
    (¬ Gate47RobustRecovery .fragile ∧ Gate47RobustRecovery .robust) ∧
    (¬ gate54TruthAligned .fragile ∧ gate54TruthAligned .robust) ∧
    Gate65Identifiable .robust .destabilized := by
  exact ⟨gate65_fragile_robust_observationally_equivalent,
    gate65_fragile_robust_not_identifiable,
    gate65_aliased_states_differ_in_robustness,
    gate65_aliased_states_differ_in_truth_alignment,
    gate65_robust_destabilized_identifiable⟩

/-!
## Gate-65 boundary

`Not identifiable` here means only: not identifiable by the specified Gate-64
sensor family. It is not an absolute unknowability theorem. A richer experiment
family could distinguish states that the current sensors alias. This distinction
will matter before Gate 66 studies repeated learning: repeated samples cannot
recover a hidden distinction that the chosen observation model never exposes.
-/

end PEL4
