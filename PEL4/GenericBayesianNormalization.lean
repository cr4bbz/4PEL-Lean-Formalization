import PEL4.BayesianBeliefStateMDP
import Init.Grind.Ring.Field
import Init.GrindInstances.Ring.Rat

namespace PEL4

/-!
# Gate 58: generic Bayesian normalization

Gate 57 normalized one concrete finite witness. Gate 58 separates the algebraic
normalization law from that witness and proves it for arbitrary finite list-based
Bayesian beliefs with nonzero total mass.
-/

/-- Sum-based rational mass, convenient for generic normalization proofs. -/
def bayesianBeliefMassSum
    {State : Type}
    (belief : BayesianEpistemicBelief State) : Rat :=
  (belief.map Prod.fst).sum

/-- Generic normalization using the sum-based mass. Impossible zero-mass beliefs
remain explicit instead of receiving invented posterior mass. -/
def normalizeBayesianBeliefGeneric
    {State : Type}
    (belief : BayesianEpistemicBelief State) : BayesianEpistemicBelief State :=
  let total := bayesianBeliefMassSum belief
  if total = 0 then belief
  else belief.map fun item => (item.1 / total, item.2)

/-- Scaling every belief weight by the same rational denominator scales total
mass by that denominator. -/
theorem bayesianBeliefMassSum_map_div
    {State : Type}
    (belief : BayesianEpistemicBelief State)
    (d : Rat) :
    bayesianBeliefMassSum
        (belief.map fun item => (item.1 / d, item.2)) =
      bayesianBeliefMassSum belief / d := by
  induction belief with
  | nil => simp [bayesianBeliefMassSum]
  | cons x xs ih =>
      simp [bayesianBeliefMassSum, ih]
      grind

/-- Main Gate-58 normalization theorem. Any finite rational belief with nonzero
total mass normalizes to total mass one. -/
theorem normalizeBayesianBeliefGeneric_mass_one
    {State : Type}
    (belief : BayesianEpistemicBelief State)
    (hMass : bayesianBeliefMassSum belief ≠ 0) :
    bayesianBeliefMassSum (normalizeBayesianBeliefGeneric belief) = 1 := by
  simp [normalizeBayesianBeliefGeneric, hMass,
    bayesianBeliefMassSum_map_div]
  grind

/-- Zero mass is kept explicit: normalization does not fabricate a probability
distribution for an impossible observation. -/
theorem normalizeBayesianBeliefGeneric_zero_mass
    {State : Type}
    (belief : BayesianEpistemicBelief State)
    (hMass : bayesianBeliefMassSum belief = 0) :
    normalizeBayesianBeliefGeneric belief = belief := by
  simp [normalizeBayesianBeliefGeneric, hMass]

/-- Gate 57's aliased prior satisfies the generic mass predicate. -/
theorem gate58_gate57_prior_mass_sum_one :
    bayesianBeliefMassSum gate57AliasedRecoveryBelief = 1 := by
  native_decide

/-- The generic normalizer leaves Gate 57's already normalized prior unchanged. -/
theorem gate58_gate57_prior_fixed :
    normalizeBayesianBeliefGeneric gate57AliasedRecoveryBelief =
      gate57AliasedRecoveryBelief := by
  native_decide

/-- Main Gate-58 bridge: Gate 57 is an instance of the generic finite
normalization theorem rather than an isolated arithmetic coincidence. -/
theorem gate58_generic_normalization_covers_gate57 :
    bayesianBeliefMassSum
      (normalizeBayesianBeliefGeneric gate57AliasedRecoveryBelief) = 1 := by
  exact normalizeBayesianBeliefGeneric_mass_one
    gate57AliasedRecoveryBelief (by native_decide)

end PEL4
