import PEL4.BayesianModelBelief
import PEL4.RobustMaximinControl

namespace PEL4

/-!
# Gate 94: Bayesian versus robust control

Bayesian model averaging and maximin robustness answer different questions.
Gate 94 exhibits both disagreement and agreement between them in the same
Gate-78 sensing problem.
-/

/-- Bayesian policy inherited from Gate 86. -/
def gate94BayesianChoice (belief : Gate86ModelBelief) : Gate78Probe :=
  gate86ChooseProbe belief

/-- Robust policy inherited from Gate 79. -/
def gate94RobustChoice : Gate78Probe := gate79RobustChoice

/-- Under an optimistic model prior Bayes accepts the fragile high-ceiling probe. -/
theorem gate94_optimistic_bayes_fragile :
    gate94BayesianChoice gate86OptimisticBelief = .fragile := by
  native_decide

/-- Maximin remains safe because it protects against the degraded model. -/
theorem gate94_robust_safe :
    gate94RobustChoice = .safe := by
  native_decide

/-- Hence optimism creates a genuine Bayesian/robust policy disagreement. -/
theorem gate94_optimistic_disagreement :
    gate94BayesianChoice gate86OptimisticBelief ≠ gate94RobustChoice := by
  native_decide

/-- With a skeptical half-half model prior, Bayesian averaging also selects safe. -/
theorem gate94_skeptical_bayes_safe :
    gate94BayesianChoice gate86SkepticalBelief = .safe := by
  native_decide

/-- Under sufficient model doubt the two decision principles coincide. -/
theorem gate94_skeptical_agreement :
    gate94BayesianChoice gate86SkepticalBelief = gate94RobustChoice := by
  native_decide

/-- Main Gate-94 theorem: robustness is not simply another spelling of Bayesian
model averaging. The policies can separate under optimism and reunite when the
Bayesian prior itself becomes sufficiently cautious. -/
theorem gate94_bayesian_robust_policy_boundary :
    gate94BayesianChoice gate86OptimisticBelief = .fragile ∧
    gate94RobustChoice = .safe ∧
    gate94BayesianChoice gate86OptimisticBelief ≠ gate94RobustChoice ∧
    gate94BayesianChoice gate86SkepticalBelief = gate94RobustChoice := by
  exact ⟨gate94_optimistic_bayes_fragile,
    gate94_robust_safe,
    gate94_optimistic_disagreement,
    gate94_skeptical_agreement⟩

/-!
## Boundary

This compares two explicit policies on a two-model finite witness. It does not
claim an equivalence theorem between robust control and any class of priors.
-/

end PEL4
