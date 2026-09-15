import PEL4.BayesianModelBelief
import PEL4.RobustMaximinControl

namespace PEL4

/-!
# Gate 94: Bayesian versus robust control
-/

def gate94BayesianChoice (belief : Gate86ModelBelief) : Gate78Probe :=
  gate86ChooseProbe belief

def gate94RobustChoice : Gate78Probe := gate79RobustChoice

theorem gate94_optimistic_bayes_fragile :
    gate94BayesianChoice gate86OptimisticBelief = .fragile := by
  native_decide

theorem gate94_robust_safe :
    gate94RobustChoice = .safe := by
  native_decide

theorem gate94_optimistic_disagreement :
    gate94BayesianChoice gate86OptimisticBelief ≠ gate94RobustChoice := by
  native_decide

theorem gate94_skeptical_bayes_safe :
    gate94BayesianChoice gate86SkepticalBelief = .safe := by
  native_decide

theorem gate94_skeptical_agreement :
    gate94BayesianChoice gate86SkepticalBelief = gate94RobustChoice := by
  native_decide

theorem gate94_bayesian_robust_policy_boundary :
    gate94BayesianChoice gate86OptimisticBelief = .fragile ∧
    gate94RobustChoice = .safe ∧
    gate94BayesianChoice gate86OptimisticBelief ≠ gate94RobustChoice ∧
    gate94BayesianChoice gate86SkepticalBelief = gate94RobustChoice := by
  exact ⟨gate94_optimistic_bayes_fragile,
    gate94_robust_safe,
    gate94_optimistic_disagreement,
    gate94_skeptical_agreement⟩

end PEL4
