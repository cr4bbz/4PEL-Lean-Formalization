import PEL4.ModalProbability.StatusTransport

/-! Focused MPFG-1 assumption audit. No project axioms, sorryAx, or native
decision axioms should occur. Run after `lake build`. -/

#print axioms PEL4.ModalProbability.evidenceStatus_raw
#print axioms PEL4.ModalProbability.SixCellProbability.coarse_untagged
#print axioms PEL4.ModalProbability.SixCellProbability.threshold_coarse
#print axioms PEL4.ModalProbability.SixCellProbability.same_coarse_same_belief
#print axioms PEL4.ModalProbability.SixCellProbability.reliability_not_determined_by_coarse
#print axioms PEL4.ModalProbability.SixCellProbability.no_reliability_reconstruction
#print axioms PEL4.ModalProbability.mixSix
#print axioms PEL4.ModalProbability.coarse_mix
#print axioms PEL4.ModalProbability.mixture_belief_commutes
#print axioms PEL4.ModalProbability.accidental_iff_not_essential
#print axioms PEL4.ModalProbability.stable_iff_essential_current
#print axioms PEL4.ModalProbability.necessary_projects
#print axioms PEL4.ModalProbability.stable_projects
#print axioms PEL4.ModalProbability.stable_iff_coarse_and_fibre_rigid
#print axioms PEL4.ModalProbability.coarse_accident_lifts
#print axioms PEL4.ModalProbability.threshold_modalities_commute
#print axioms PEL4.ModalProbability.existing_K_stability_commutes
#print axioms PEL4.ModalProbability.existing_K_value_commutes
#print axioms PEL4.ModalProbability.finite_chain_preserves_threshold
#print axioms PEL4.ModalProbability.everywhere_s5
#print axioms PEL4.ModalProbability.coarse_stable_fine_accidental
#print axioms PEL4.ModalProbability.probability_profile_projection_hides_instability
#print axioms PEL4.ModalProbability.stable_B_does_not_mean_constant_mass
#print axioms PEL4.ModalProbability.refinement_retains_B_and_N
